"""Archive and contract regressions; no mathematical proof is checked here."""
import copy, hashlib, importlib.util, io, json, re, stat, tempfile, unittest, warnings, zipfile
from pathlib import Path
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('argonaut_replay',ROOT/'verifier/argonaut/replay.py')
replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay)
sha=lambda b:hashlib.sha256(b).hexdigest()

def zip_bytes(entries):
    stream=io.BytesIO()
    with zipfile.ZipFile(stream,'w',zipfile.ZIP_DEFLATED) as archive:
        for name,data,kind in entries:
            member=zipfile.ZipInfo(name);member.external_attr=(kind|0o600)<<16
            with warnings.catch_warnings():
                warnings.simplefilter('ignore',UserWarning)
                archive.writestr(member,data)
    return stream.getvalue()

def bundle(extra=()):
    proof=b'theorem harmless : True := trivial\n'
    inner=zip_bytes([('project/Main.lean',proof,stat.S_IFREG),*extra])
    manifest=b'{"fixture":true}\n'
    outer=zip_bytes([('Lean_Proof/provenance/SOURCE-MANIFEST.json',manifest,stat.S_IFREG),('Lean_Proof/overlay.zip',inner,stat.S_IFREG)])
    pins={'release':{'bytes':len(outer),'sha256':sha(outer),'manifest_sha256':sha(manifest),'overlay_path':'Lean_Proof/overlay.zip','overlay_sha256':sha(inner)},
          'source_manifest':[{'module':'Main','source':'project/Main.lean','path':'Main.lean','sha256':sha(proof),'bytes':len(proof)}]}
    return outer,pins,proof

class DataSafety(unittest.TestCase):
    def test_author_scripts_are_never_executed(self):
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw);marker=root/'executed'
            code=f'from pathlib import Path\nPath({str(marker)!r}).touch()'.encode()
            payload,pins,proof=bundle([('project/reconstruct.py',code,stat.S_IFREG)])
            with patch('subprocess.run',side_effect=AssertionError('execution')),patch('subprocess.check_output',side_effect=AssertionError('execution')):
                result=replay.unpack_release(payload,pins,root/'source')
            self.assertEqual(result,{'Main.lean':sha(proof)})
            self.assertFalse(marker.exists())
            self.assertEqual((root/'source/Main.lean').read_bytes(),proof)

    def test_stale_release_source_or_nested_manifest_hashes_fail(self):
        payload,pins,_=bundle()
        for section,key in [('release','sha256'),('release','manifest_sha256'),('release','overlay_sha256'),('source','sha256')]:
            changed=copy.deepcopy(pins)
            (changed['source_manifest'][0] if section=='source' else changed['release'])[key]='0'*64
            with self.subTest(key=key),tempfile.TemporaryDirectory() as raw,self.assertRaises(ValueError):
                replay.unpack_release(payload,changed,Path(raw))

    def test_unsafe_unused_paths_links_and_duplicates_fail(self):
        entries=[(p,b'x',stat.S_IFREG) for p in ['../escape','/absolute','project/../../escape','project\\escape','project//escape','./project/escape','project/\nfile']]
        entries += [('project/link',b'../escape',stat.S_IFLNK),('project/Main.lean',b'changed',stat.S_IFREG)]
        for entry in entries:
            payload,pins,_=bundle([entry])
            with self.subTest(entry=entry[0]),tempfile.TemporaryDirectory() as raw,self.assertRaises(ValueError):
                replay.unpack_release(payload,pins,Path(raw))

    def test_missing_or_escaping_source_destination_fails(self):
        payload,pins,_=bundle()
        for field,value in [('source','project/Missing.lean'),('path','../escape'),('path','Wrong.lean')]:
            changed=copy.deepcopy(pins);changed['source_manifest'][0][field]=value
            with self.subTest(field=field),tempfile.TemporaryDirectory() as raw,self.assertRaises((ValueError,KeyError)):
                replay.unpack_release(payload,changed,Path(raw))

    def test_existing_output_is_not_overwritten(self):
        payload,pins,_=bundle()
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw);(root/'Main.lean').write_text('preserve')
            with self.assertRaisesRegex(ValueError,'overwrite'):replay.unpack_release(payload,pins,root)
            self.assertEqual((root/'Main.lean').read_text(),'preserve')

    def test_zip_resource_limits_are_checked_before_member_read(self):
        payload=zip_bytes([('one',b'123',stat.S_IFREG),('two',b'456',stat.S_IFREG)])
        for limits in [(1,100,100),(10,5,100),(10,100,2)]:
            with self.subTest(limits=limits),self.assertRaisesRegex(ValueError,'resource limit'):
                replay.checked_zip(payload,count_limit=limits[0],byte_limit=limits[1],member_limit=limits[2])

    def test_exact_canonical_all_dirichlet_contract(self):
        challenge,solution=replay.canonical_sources()
        template=(ROOT/'verifier/upstream-challenge.lean').read_text()
        reference=template.split('theorem LFunction_ne_zero_of_seven_eighths_lt_re',1)[1].split(':= by',1)[0].replace('(7 / 8 : ℝ)','(3499999 / 4000000 : ℝ)')
        statement=challenge.split('theorem allDirichlet',1)[1].split(':= by',1)[0]
        normalize=lambda s:re.sub(r'\s+','',s.replace('_root_.',''))
        self.assertEqual(normalize(reference),normalize(statement))
        self.assertNotIn('PerturbedBoundary',challenge)
        self.assertNotIn('sorry',solution)
        self.assertEqual(replay.AXIOMS,{'propext','Classical.choice','Quot.sound'})

    def test_unsupported_host_fails_before_loading_inputs(self):
        with patch.object(replay.sys,'platform','darwin'),patch('subprocess.run',side_effect=AssertionError('spawn')),tempfile.TemporaryDirectory() as raw:
            with self.assertRaisesRegex(ValueError,'unprivileged Linux'):replay.run(Path(raw)/'absent',Path(raw)/'work')
            self.assertFalse((Path(raw)/'work').exists())

    def test_candidate_logs_cannot_be_links_to_host_files(self):
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw);work=root/'run';work.mkdir();outside=root/'private';outside.write_text('review fixture')
            log=work/'leak.log';log.symlink_to(outside)
            with patch.object(replay,'digest',side_effect=AssertionError('read escaped artifact')):
                with self.assertRaisesRegex(ValueError,'symlink'):replay.artifact_inventory(work,[log])
            folder=work/'logs';folder.symlink_to(root,target_is_directory=True)
            with self.assertRaisesRegex(ValueError,'symlink'):replay.artifact_inventory(work,[folder/'private'])

    def test_diagnostic_size_is_checked_before_hashing(self):
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw);log=root/'large.log'
            with log.open('wb') as output:output.truncate(12*1024**2+1)
            with patch.object(replay,'digest',side_effect=AssertionError('hashed oversized artifact')):
                with self.assertRaisesRegex(ValueError,'resource limit'):replay.artifact_inventory(root,[log])

if __name__=='__main__':unittest.main()
