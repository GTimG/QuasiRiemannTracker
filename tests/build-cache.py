"""Regression and archive authentication tests adapted from PR #35."""
from pathlib import Path
import copy, importlib.util, io, json, os, shutil, subprocess, sys, tarfile, tempfile, unittest
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'verifier'))
from standard.build_cache import build_inputs, pack_cache, restore_cache, restore_shards, shard_of, digest, compatibility_error
import standard.build_cache as build_cache
spec = importlib.util.spec_from_file_location('restore_build', ROOT/'verifier/actions/restore-build.py')
restore = importlib.util.module_from_spec(spec)
spec.loader.exec_module(restore)
spec = importlib.util.spec_from_file_location('plan_cache', ROOT/'verifier/actions/plan-cache.py')
plan_cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(plan_cache)
spec = importlib.util.spec_from_file_location('publish_cache', ROOT/'verifier/actions/publish-cache.py')
publish_cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publish_cache)
import cache_release


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

    def multipart_publication(self):
        out, keys = self.publication()
        # Keep the test small while reproducing a logical shard larger than the
        # extractor's hard cap. Every part must independently fit that same cap.
        modules = {f'Submissions.base.Part{i}': str(i)*64 for i in range(5)}
        keys['modules'] = modules
        for module in modules:
            base = out/'run/candidate-lib'/(module.replace('.', '/')+'.olean')
            base.write_bytes(b'compiled'*375)
            Path(str(base)+'.private').write_bytes(b'private')
            Path(str(base)+'.server').write_bytes(b'server')
        plan = out/'cache-plan.json'
        value = json.loads(plan.read_text())
        value['keys'] = keys
        plan.write_text(json.dumps(value))
        inputs = out/'run/build-inputs.json'
        inputs.write_text(json.dumps(keys))
        result = out/'run/build-result.json'
        value = json.loads(result.read_text())
        value['build_inputs_sha256'] = digest(inputs)
        result.write_text(json.dumps(value))
        patch.object(publish_cache, 'PART_PAYLOAD_BYTES', 6500).start()
        patch.object(build_cache, 'MAX_BYTES', 12000).start()
        return out, keys

    def test_oversized_logical_shard_splits_and_restores_every_product(self):
        out, keys = self.multipart_publication()
        # The old single-archive implementation fails with the exact same data.
        with self.assertRaisesRegex(ValueError, 'size limits'):
            publish_cache.pack_part(keys['modules'], keys, out/'run/candidate-lib', self.root)
        publish_cache.prepare()
        _, index, archives = publish_cache.validate_bundle(out/'cache-publication')
        self.assertEqual(index['schema_version'], 3)
        self.assertEqual(len(archives), 3)
        parts = index['shards']['Submissions.base']['parts']
        self.assertEqual([len(p['modules']) for p in parts], [2, 2, 1])
        downloaded = self.root/'downloaded'
        downloaded.mkdir()
        def fetch(url, target, limit):
            source = out/'cache-publication'/url.rsplit('/', 1)[1]
            self.assertLessEqual(source.stat().st_size, limit)
            shutil.copyfile(source, target)
        fetched = cache_release.fetch_shards(index, ['Submissions.base'], downloaded, fetch)
        restored = self.root/'multipart-lib'
        self.assertEqual(restore_shards({'shards':fetched}, restored, keys), set(keys['modules']))
        for module in keys['modules']:
            for suffix in build_cache.SUFFIXES:
                relative = module.replace('.', '/')+suffix
                self.assertEqual((restored/relative).read_bytes(), (out/'run/candidate-lib'/relative).read_bytes())

    def test_partitions_are_bounded_and_reject_oversized_single_modules(self):
        out, keys = self.multipart_publication()
        lib = out/'run/candidate-lib'
        with patch.object(publish_cache, 'MAX_FILES', 4):
            self.assertEqual(len(list(publish_cache.module_parts(keys['modules'], lib))), 5)
        with patch.object(publish_cache, 'PART_PAYLOAD_BYTES', 3013):
            self.assertEqual(len(list(publish_cache.module_parts(keys['modules'], lib))), 5)
        with patch.object(publish_cache, 'PART_PAYLOAD_BYTES', 3012), self.assertRaisesRegex(ValueError, 'One module'):
            list(publish_cache.module_parts(keys['modules'], lib))

    def test_multipart_index_rejects_missing_duplicate_foreign_and_oversized_parts(self):
        out, _ = self.multipart_publication()
        publish_cache.prepare()
        original = json.loads((out/'cache-publication/cache.json').read_text())
        for attack in ['missing', 'duplicate', 'wrong-key', 'foreign', 'path', 'oversized', 'empty', 'ambiguous']:
            index = copy.deepcopy(original)
            shard = index['shards']['Submissions.base']
            parts = shard['parts']
            if attack == 'missing': parts.pop()
            if attack == 'duplicate': parts.append(copy.deepcopy(parts[0]))
            if attack == 'wrong-key': parts[0]['modules'][next(iter(parts[0]['modules']))] = 'f'*64
            if attack == 'foreign': parts[0]['modules']['Submissions.foreign.X'] = 'f'*64
            if attack == 'path': parts[0]['archive'] = '../escape'
            if attack == 'oversized': parts[0]['size'] = cache_release.PART_ARCHIVE_BYTES+1
            if attack == 'empty': shard['parts'] = []
            if attack == 'ambiguous': shard['archive'] = parts[0]['archive']
            with self.subTest(attack=attack), self.assertRaises(ValueError):
                cache_release.validate_index(index)

    def test_part_inventory_cannot_claim_modules_from_another_archive(self):
        out, _ = self.multipart_publication()
        publish_cache.prepare()
        path = out/'cache-publication/cache.json'
        value = json.loads(path.read_text())
        parts = value['shards']['Submissions.base']['parts']
        # The union is still correct and archive hashes still match, but the
        # signed module-to-archive assignment would be false.
        parts[0]['modules'], parts[1]['modules'] = parts[1]['modules'], parts[0]['modules']
        path.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, 'inputs differ'):
            publish_cache.validate_bundle(out/'cache-publication')

    def test_multipart_download_rejects_tampered_piece(self):
        out, _ = self.multipart_publication()
        publish_cache.prepare()
        value = json.loads((out/'cache-publication/cache.json').read_text())
        with self.assertRaisesRegex(ValueError, 'archive differs'):
            cache_release.fetch_shards(value, ['Submissions.base'], self.root,
                fetch=lambda url,path,limit:path.write_bytes(b'wrong'))

    def test_legacy_index_is_rebuilt_as_bounded_parts(self):
        keys = {**self.inputs, 'modules': {'Submissions.base.Main':self.inputs['modules']['Submissions.base.Main']}}
        shard = {'modules':keys['modules']}
        _, _, changed, _ = plan_cache.plan(keys, {'schema_version':2,
            'environment':keys['environment'], 'shards':{'Submissions.base':shard}})
        self.assertEqual(changed, ['Submissions.base'])

    def test_unchanged_multipart_shard_is_preserved_without_repackaging(self):
        out, keys = self.multipart_publication()
        publish_cache.prepare()
        original = json.loads((out/'cache-publication/cache.json').read_text())
        _, _, changed, removed = plan_cache.plan(keys, original)
        self.assertEqual((changed, removed), ([], []))
        path = out/'cache-plan.json'
        value = json.loads(path.read_text())
        value.update(previous=original['shards'], changed=[])
        path.write_text(json.dumps(value))
        shutil.rmtree(out/'cache-publication')
        publish_cache.prepare()
        _, index, archives = publish_cache.validate_bundle(out/'cache-publication')
        self.assertEqual(index['shards'], original['shards'])
        self.assertEqual(archives, [])

    def test_manifest_counts_toward_unchanged_extraction_limit(self):
        with patch.object(build_cache, 'MAX_BYTES', 100), self.assertRaisesRegex(ValueError, 'size limits'):
            pack_cache(self.library, self.archive, self.inputs)

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
        out, _ = self.multipart_publication()
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
        self.assertEqual(len(uploaded), 5)  # Three bounded pieces plus index/signature.
        published = json.loads(uploaded['cache.json'])
        self.assertEqual(published['schema_version'], 3)
        saved_index, saved_sig = self.root/'downloaded.json', self.root/'downloaded.sig'
        saved_index.write_bytes(uploaded['cache.json'])
        saved_sig.write_bytes(uploaded['cache.sig'])
        self.assertEqual(cache_release.authenticate(saved_index, saved_sig, public), published)
        published['shards']['Submissions.base']['parts'].pop()
        saved_index.write_text(json.dumps(published))
        with self.assertRaises(subprocess.CalledProcessError):
            cache_release.authenticate(saved_index, saved_sig, public)


unittest.main()
