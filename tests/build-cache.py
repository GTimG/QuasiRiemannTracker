"""Regression and archive authentication tests adapted from PR #35."""
from pathlib import Path
import copy, importlib.util, io, json, os, shutil, subprocess, sys, tarfile, tempfile, unittest
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'verifier'))
from standard.build_cache import build_inputs, pack_cache, restore_cache, restore_shards, shard_of, digest, compatibility_error
spec = importlib.util.spec_from_file_location('restore_build', ROOT/'verifier/actions/restore-build.py')
restore = importlib.util.module_from_spec(spec)
spec.loader.exec_module(restore)
spec = importlib.util.spec_from_file_location('plan_cache', ROOT/'verifier/actions/plan-cache.py')
plan_cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(plan_cache)
spec = importlib.util.spec_from_file_location('publish_cache', ROOT/'verifier/actions/publish-cache.py')
publish_cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publish_cache)


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.contract = {'build_order':['Submissions.base.Main','Candidate.Main'],
            'module_dependencies':{'Submissions.base.Main':[], 'Candidate.Main':['Submissions.base.Main']},
            'source_files':{'src/Submissions/base/Main.lean':'base', 'src/Candidate/Main.lean':'main'}}
        self.inputs = self.inputs_for(self.contract)
        self.library = self.root/'lib'
        for module in self.contract['build_order']:
            p = self.library/(module.replace('.','/')+'.olean')
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(module.encode())
            Path(str(p)+'.private').write_bytes(b'private')
            Path(str(p)+'.server').write_bytes(b'server')
        self.archive = self.root/'cache.tar.gz'
        pack_cache(self.library, self.archive, self.inputs)

    def inputs_for(self, contract=None, root='/worker', compiler='compiler', dep='mathlib'):
        return build_inputs(contract or self.contract, {'libraries':[root+'/lib']},
            {root+'/lib/Mathlib.olean':dep}, {'source_lean':compiler})

    def test_round_trip(self):
        selected = restore_cache(self.archive, self.root/'restored', self.inputs)
        self.assertEqual(selected, set(self.contract['build_order']))
        self.assertEqual((self.root/'restored/Candidate/Main.olean.private').read_bytes(), b'private')

    def test_changed_source_keeps_shared_dependency(self):
        changed = copy.deepcopy(self.contract)
        changed['source_files']['src/Candidate/Main.lean'] = 'new theorem'
        selected = restore_cache(self.archive, self.root/'restored', self.inputs_for(changed))
        self.assertEqual(selected, {'Submissions.base.Main'})
        self.assertFalse((self.root/'restored/Candidate/Main.olean').exists())

    def test_dependency_change_invalidates_importers(self):
        changed = copy.deepcopy(self.contract)
        changed['source_files']['src/Submissions/base/Main.lean'] = 'changed'
        self.assertEqual(restore_cache(self.archive,self.root/'restored',self.inputs_for(changed)), set())

    def test_metadata_and_commit_do_not_invalidate_modules(self):
        changed = copy.deepcopy(self.contract)
        changed['head_sha'] = 'new head'
        changed['source_files']['metadata.json'] = 'new metadata'
        self.assertEqual(self.inputs, self.inputs_for(changed))

    def test_compiler_and_library_invalidation(self):
        for inputs in [self.inputs_for(compiler='changed'), self.inputs_for(dep='changed')]:
            with self.assertRaisesRegex(ValueError, 'compiler or libraries'):
                restore_cache(self.archive, self.root/'restored', inputs)

    def test_paths_and_library_grouping_are_portable(self):
        self.assertEqual(self.inputs, self.inputs_for(root='/server'))
        grouped = build_inputs(self.contract, {'libraries':['/one','/two']},
            {'/one/Mathlib.olean':'mathlib','/two/Index.ilean':'editor-data'}, {'source_lean':'compiler'})
        self.assertEqual(self.inputs, grouped)

    def test_companion_files_invalidate_and_explain_server_worker_mismatch(self):
        worker = build_inputs(self.contract, {'libraries':['/worker/lib']},
            {'/worker/lib/Mathlib.olean':'mathlib', '/worker/lib/Mathlib.olean.private':'private'},
            {'source_lean':'compiler'})
        self.assertNotEqual(worker['environment'], self.inputs['environment'])
        self.assertIn('1 worker-only library files: Mathlib.olean.private',
                      compatibility_error(self.inputs, worker))
        with self.assertRaisesRegex(ValueError, 'Mathlib.olean.private'):
            restore_cache(self.archive, self.root/'restored', worker)
        self.assertFalse((self.root/'restored').exists())

    def test_library_precedence_and_directory_boundaries(self):
        grouped = build_inputs(self.contract, {'libraries':['/z/first','/a/second']},
            {'/z/first/Mathlib.olean':'mathlib', '/a/second/Mathlib.olean':'shadowed',
             '/z/first-other/Extra.olean':'outside'}, {'source_lean':'compiler'})
        self.assertEqual(self.inputs, grouped)

    def test_mismatch_identifies_changed_and_missing_libraries(self):
        worker = build_inputs(self.contract, {'libraries':['/worker/lib']},
            {'/worker/lib/Mathlib.olean':'changed','/worker/lib/Extra.olean':'extra'},
            {'source_lean':'other-compiler'})
        reason = compatibility_error(worker, self.inputs)
        self.assertIn('source compiler differs', reason)
        self.assertIn('1 cache-only library files: Extra.olean', reason)
        self.assertIn('1 changed library files: Mathlib.olean', reason)

    def rewrite(self, transform):
        with tarfile.open(self.archive) as source:
            members = [(m, source.extractfile(m).read()) for m in source]
        transform(members)
        with tarfile.open(self.archive, 'w:gz') as target:
            for member, data in members:
                member.size = len(data)
                target.addfile(member, io.BytesIO(data))

    def test_corrupted_output_leaves_no_importable_files(self):
        self.rewrite(lambda members:members.__setitem__(-1,(members[-1][0],b'corrupt')))
        with self.assertRaisesRegex(ValueError,'checksum'):
            restore_cache(self.archive,self.root/'restored',self.inputs)
        self.assertFalse(list((self.root/'restored').rglob('*.olean')))

    def test_rejects_archive_attacks(self):
        for attack in ['traversal','symlink','hardlink','duplicate','missing']:
            pack_cache(self.library,self.archive,self.inputs)
            def change(members):
                if attack == 'traversal':members[1][0].name='../escape'
                if attack == 'symlink':members[1][0].type=tarfile.SYMTYPE
                if attack == 'hardlink':members[1][0].type=tarfile.LNKTYPE
                if attack == 'duplicate':members.append(members[1])
                if attack == 'missing':members.pop()
            self.rewrite(change)
            with self.subTest(attack=attack),self.assertRaises(ValueError):
                restore_cache(self.archive,self.root/'bad',self.inputs)
        self.assertFalse((self.root/'escape').exists())

    def test_rejects_invalid_module_graph(self):
        changed = copy.deepcopy(self.contract)
        changed['module_dependencies']['Submissions.base.Main']=['Candidate.Main']
        with self.assertRaisesRegex(ValueError,'ordering'):
            self.inputs_for(changed)

    def test_incompatible_signed_index_skips_large_download(self):
        out = self.root/'verification'
        (out/'prepared').mkdir(parents=True)
        (out/'profile.json').write_text(json.dumps({'libraries':['/worker/lib']}))
        (out/'prepared/contract.json').write_text(json.dumps(self.contract))
        (out/'prepared/libraries.json').write_text(json.dumps({'/worker/lib/Mathlib.olean':'mathlib'}))
        (out/'tool-pins.json').write_text(json.dumps({'source_lean':'compiler'}))
        previous = Path.cwd()
        try:
            os.chdir(self.root)
            with patch.object(restore, 'download') as download, patch.object(restore, 'authenticate',
                    return_value={'environment':'different','shards':{}}):
                restore.main()
                self.assertEqual(download.call_count, 2)
            self.assertNotIn('candidate_cache',json.loads((out/'profile.json').read_text()))
            status = json.loads((out/'build-cache-status.json').read_text())
            self.assertEqual(status['status'], 'miss')
            self.assertIn('compiler or libraries differ', status['reason'])
            self.assertEqual(status['worker_environment'], self.inputs['environment'])
        finally:
            os.chdir(previous)

    def test_signature_binds_archive_and_rejects_wrong_key(self):
        key, public = self.root/'key.pem',self.root/'public.pem'
        subprocess.run(['openssl','genpkey','-algorithm','ED25519','-out',str(key)],check=True)
        subprocess.run(['openssl','pkey','-in',str(key),'-pubout','-out',str(public)],check=True)
        sha=digest(self.archive)
        index=self.root/'cache.json';signature=self.root/'cache.sig'
        shard={'archive':sha+'.tar.gz','sha256':sha,'size':self.archive.stat().st_size,
               'modules':{'Submissions.base.Main':self.inputs['modules']['Submissions.base.Main']}}
        index.write_text(json.dumps({'schema_version':2,'shards':{'Submissions.base':shard}}))
        subprocess.run(['openssl','pkeyutl','-sign','-inkey',str(key),'-rawin','-in',str(index),'-out',str(signature)],check=True)
        self.assertEqual(restore.authenticate(index,signature,public)['shards']['Submissions.base']['sha256'],sha)
        with self.assertRaises(subprocess.CalledProcessError):
            restore.authenticate(index,signature)  # Production key cannot accept a test signature.
        index.write_text(index.read_text()+' ')
        with self.assertRaises(subprocess.CalledProcessError):
            restore.authenticate(index,signature,public)


    def test_shards_restore_together_and_reject_misfiled_modules(self):
        shared = {'Submissions.base.Main': self.inputs['modules']['Submissions.base.Main']}
        shard = self.root/'shard.tar.gz'
        staged = self.root/'staged'
        for suffix in ['.olean', '.olean.private', '.olean.server']:
            (staged/'Submissions/base').mkdir(parents=True, exist_ok=True)
            (staged/('Submissions/base/Main'+suffix)).write_bytes((self.library/('Submissions/base/Main'+suffix)).read_bytes())
        pack_cache(staged, shard, {**self.inputs, 'modules': shared})
        cache = {'shards': [{'path': str(shard), 'sha256': digest(shard)}]}
        self.assertEqual(restore_shards(cache, self.root/'restored', self.inputs), {'Submissions.base.Main'})
        cache['shards'][0]['sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError, 'changed'):
            restore_shards(cache, self.root/'again', self.inputs)
        self.assertEqual(shard_of('Submissions.base.Deep.Main'), 'Submissions.base')
        for module in ['Candidate.Main', 'Submissions.base']:
            with self.assertRaises(ValueError):
                shard_of(module)

    def test_plan_rebuilds_only_changed_shards(self):
        contract = {'build_order':['Submissions.a.X','Submissions.b.Y'],
            'module_dependencies':{'Submissions.a.X':[], 'Submissions.b.Y':['Submissions.a.X']},
            'source_files':{'src/Submissions/a/X.lean':'x', 'src/Submissions/b/Y.lean':'y'}}
        keys = self.inputs_for(contract)
        shards = {name: {'modules': modules} for name, modules in
                  [('Submissions.a', {'Submissions.a.X': keys['modules']['Submissions.a.X']}),
                   ('Submissions.b', {'Submissions.b.Y': keys['modules']['Submissions.b.Y']}),
                   ('Submissions.gone', {'Submissions.gone.Z': '0'*64})]}
        index = {'environment': keys['environment'], 'shards': shards}
        _, _, changed, removed = plan_cache.plan(keys, index)
        self.assertEqual((changed, removed), ([], ['Submissions.gone']))
        # A scheduled/manual full rebuild keeps previous archives for active readers,
        # but cannot restore any current shard from the previous compilation.
        _, previous, changed, removed = plan_cache.plan(keys, index, rebuild_all=True)
        self.assertEqual(previous, shards)
        self.assertEqual(changed, ['Submissions.a', 'Submissions.b'])
        self.assertEqual(removed, ['Submissions.gone'])
        _, _, changed, _ = plan_cache.plan(keys, None)
        self.assertEqual(changed, ['Submissions.a', 'Submissions.b'])
        contract['source_files']['src/Submissions/a/X.lean'] = 'changed'
        # A changed import changes its importers' keys, so both shards rebuild.
        _, _, changed, _ = plan_cache.plan(self.inputs_for(contract), index)
        self.assertEqual(changed, ['Submissions.a', 'Submissions.b'])
        _, previous, changed, _ = plan_cache.plan(keys, {**index, 'environment': 'other'})
        self.assertEqual((previous, changed), ({}, ['Submissions.a', 'Submissions.b']))
        self.assertEqual(plan_cache.closure(['Submissions.b.Y'], contract['module_dependencies']),
                         {'Submissions.a.X', 'Submissions.b.Y'})

    def publication(self):
        out = self.root/'verification'
        (out/'run').mkdir(parents=True)
        shutil.copytree(self.library, out/'run/candidate-lib')
        keys = {**self.inputs, 'modules': {m:k for m,k in self.inputs['modules'].items()
                                         if m.startswith('Submissions.')}}
        head = 'a'*40
        plan = {'head_sha':head, 'keys':keys, 'previous':{}, 'changed':['Submissions.base'], 'removed':[]}
        (out/'cache-plan.json').write_text(json.dumps(plan))
        inputs = out/'run/build-inputs.json'
        inputs.write_text(json.dumps(keys))
        (out/'run/build-result.json').write_text(json.dumps({'status':'BUILT', 'head_sha':head,
            'build_inputs_sha256':digest(inputs)}))
        self.addCleanup(patch.stopall)
        patch.object(publish_cache, 'OUT', out).start()
        patch.dict(os.environ, {'GITHUB_SHA':head}).start()
        return out, keys

    def test_publication_round_trip_without_secrets_in_builder(self):
        out, keys = self.publication()
        with patch.dict(os.environ, {}, clear=True):
            os.environ['GITHUB_SHA'] = 'a'*40
            publish_cache.prepare()
        plan, index, archives = publish_cache.validate_bundle(out/'cache-publication')
        self.assertEqual(plan['keys'], keys)
        self.assertEqual(set(index['shards']), {'Submissions.base'})
        self.assertEqual(len(archives), 1)
        self.assertEqual(restore_cache(archives[0], self.root/'published-lib', keys), set(keys['modules']))
        self.assertFalse((self.root/'published-lib/Candidate').exists())

    def test_publication_rejects_stale_commit_and_inputs(self):
        out, _ = self.publication()
        with patch.dict(os.environ, {'GITHUB_SHA':'b'*40}), self.assertRaisesRegex(ValueError, 'another commit'):
            publish_cache.prepare()
        (out/'run/build-inputs.json').write_text((out/'run/build-inputs.json').read_text()+' ')
        with self.assertRaisesRegex(ValueError, 'does not match'):
            publish_cache.prepare()

    def test_publication_rejects_missing_build_module(self):
        out, _ = self.publication()
        inputs = out/'run/build-inputs.json'
        value = json.loads(inputs.read_text())
        value['modules'] = {}
        inputs.write_text(json.dumps(value))
        result = out/'run/build-result.json'
        value = json.loads(result.read_text())
        value['build_inputs_sha256'] = digest(inputs)
        result.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, 'does not match'):
            publish_cache.prepare()

    def test_publication_rejects_symlinked_compiler_output(self):
        out, _ = self.publication()
        product = out/'run/candidate-lib/Submissions/base/Main.olean'
        product.unlink()
        product.symlink_to(self.library/'Submissions/base/Main.olean')
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            publish_cache.prepare()

    def test_publisher_rejects_tampered_archive_before_remote_write(self):
        out, _ = self.publication()
        publish_cache.prepare()
        archive = next((out/'cache-publication').glob('*.tar.gz'))
        archive.write_bytes(b'tampered')
        with patch.object(publish_cache, 'api') as remote, self.assertRaisesRegex(ValueError, 'checksum'):
            publish_cache.main()
        remote.assert_not_called()

    def test_publisher_signs_with_matching_key_and_downloads_published_outputs(self):
        out, _ = self.publication()
        publish_cache.prepare()
        key, public = self.root/'key.pem', self.root/'public.pem'
        subprocess.run(['openssl','genpkey','-algorithm','ED25519','-out',str(key)],check=True)
        subprocess.run(['openssl','pkey','-in',str(key),'-pubout','-out',str(public)],check=True)
        with patch.dict(os.environ, {'QRH_BUILD_CACHE_KEY':key.read_text(),'GH_TOKEN':'test-token'}), \
                patch.object(publish_cache, 'api') as remote, self.assertRaises(subprocess.CalledProcessError):
            publish_cache.main()  # Test key does not match the production pin.
        remote.assert_not_called()
        uploaded = {}
        def upload(_release, path, _token):
            uploaded[path.name] = path.read_bytes()
        def download(url, destination, limit):
            data = uploaded[url.rsplit('/', 1)[1]]
            self.assertLessEqual(len(data), limit)
            destination.write_bytes(data)
        import cache_release
        with patch.dict(os.environ, {'QRH_BUILD_CACHE_KEY':key.read_text(),'GH_TOKEN':'test-token'}), \
                patch.object(publish_cache, 'KEY', public), \
                patch.object(publish_cache, 'release', return_value={'assets':[]}), \
                patch.object(publish_cache, 'api', return_value={'assets':[]}), \
                patch.object(publish_cache, 'upload', side_effect=upload), \
                patch.object(publish_cache, 'download', side_effect=download), \
                patch.object(publish_cache, 'fetch_shards', side_effect=lambda i,n,d:cache_release.fetch_shards(i,n,d,download)):
            publish_cache.main()
        self.assertEqual(list(uploaded)[-2:], ['cache.json', 'cache.sig'])
        self.assertEqual(len(uploaded), 3)


unittest.main()
