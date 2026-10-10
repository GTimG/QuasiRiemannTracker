"""Source binding, ingestion and contract tests; no Lean execution on the host."""
import copy,hashlib,importlib.util,io,json,re,stat,tempfile,unittest,warnings,zipfile
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'verifier/akashlevy/replay.py');replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay)
sha=lambda b:hashlib.sha256(b).hexdigest()
def bundle(extra=()):
    data=b'theorem harmless : True := trivial\n';stream=io.BytesIO()
    with zipfile.ZipFile(stream,'w',zipfile.ZIP_DEFLATED) as z:
        for name,value,kind in [('WeightedQRH/Main.lean',data,stat.S_IFREG),*extra]:
            info=zipfile.ZipInfo(name);info.external_attr=(kind|0o644)<<16
            with warnings.catch_warnings():
                warnings.simplefilter('ignore',UserWarning);z.writestr(info,value)
    payload=stream.getvalue()
    return payload,{'source_bundle':{'bytes':len(payload),'sha256':sha(payload)},'source_manifest':[{'module':'WeightedQRH.Main','path':'WeightedQRH/Main.lean','bytes':len(data),'sha256':sha(data)}]}
class Safety(unittest.TestCase):
    def test_authenticates_sources_without_executing_them(self):
        data,pins=bundle()
        with tempfile.TemporaryDirectory() as d,patch('subprocess.run',side_effect=AssertionError('execution')):
            self.assertEqual(replay.unpack_source(data,pins,Path(d)),{'WeightedQRH/Main.lean':pins['source_manifest'][0]['sha256']})
    def test_stale_bundle_module_or_size_rejected(self):
        data,pins=bundle()
        for section,key,value in [('bundle','sha256','0'*64),('bundle','bytes',1),('source','sha256','0'*64),('source','bytes',1)]:
            p=copy.deepcopy(pins);(p['source_bundle'] if section=='bundle' else p['source_manifest'][0])[key]=value
            with self.subTest(key=key),tempfile.TemporaryDirectory() as d,self.assertRaises(ValueError):replay.unpack_source(data,p,Path(d))
    def test_unsafe_paths_links_duplicates_and_unlisted_files_rejected(self):
        for name,kind in [('../escape',stat.S_IFREG),('/escape',stat.S_IFREG),('x\\y',stat.S_IFREG),('x//y',stat.S_IFREG),('x/link',stat.S_IFLNK),('WeightedQRH/Main.lean',stat.S_IFREG),('author.py',stat.S_IFREG)]:
            data,pins=bundle([(name,b'bad',kind)])
            with self.subTest(name=name),tempfile.TemporaryDirectory() as d,self.assertRaises(ValueError):replay.unpack_source(data,pins,Path(d))
    def test_existing_file_not_overwritten(self):
        data,pins=bundle()
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'WeightedQRH').mkdir();(root/'WeightedQRH/Main.lean').write_text('preserve')
            with self.assertRaisesRegex(ValueError,'overwrite'):replay.unpack_source(data,pins,root)
    def test_contract_is_exact_upstream_with_only_the_rational_changed(self):
        challenge,solution=replay.canonical_sources();template=(ROOT/'verifier/upstream-challenge.lean').read_text()
        reference=template.split('theorem LFunction_ne_zero_of_seven_eighths_lt_re',1)[1].split(':= by',1)[0].replace('(7 / 8 : ℝ)','(10499 / 12000 : ℝ)')
        statement=challenge.split('theorem allDirichlet',1)[1].split(':= by',1)[0]
        normalize=lambda s:re.sub(r'\s+','',s.replace('_root_.',''))
        self.assertEqual(normalize(reference),normalize(statement));self.assertNotIn('WeightedQRH',challenge);self.assertNotIn('sorry',solution)
        self.assertEqual(replay.AXIOMS,{'propext','Classical.choice','Quot.sound'})
    def test_unsupported_host_fails_before_reading_inputs(self):
        with patch.object(replay.sys,'platform','darwin'),tempfile.TemporaryDirectory() as d:
            with self.assertRaisesRegex(ValueError,'unprivileged Linux'):replay.run(Path(d)/'absent',Path(d)/'work')
            self.assertFalse((Path(d)/'work').exists())
    def test_host_paths_and_oversized_diagnostics_cannot_be_collected(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);outside=root/'private';outside.write_text('private');work=root/'run';work.mkdir();log=work/'log';log.symlink_to(outside)
            with patch.object(replay,'digest',side_effect=AssertionError('host read')):
                with self.assertRaisesRegex(ValueError,'symlink'):replay.artifact_inventory(work,[log])
            log.unlink()
            with log.open('wb') as f:f.truncate(12*1024**2+1)
            with self.assertRaisesRegex(ValueError,'resource limit'):replay.artifact_inventory(work,[log])
    def test_complete_bundle_pins_all_228_submission_modules(self):
        pins=json.loads((ROOT/'verifier/akashlevy/pins.json').read_text());rows=pins['source_manifest']
        self.assertEqual(len(rows),2898);self.assertEqual(sum(r['origin']=='submission' for r in rows),228)
        for r in rows:
            if r['origin']=='submission':self.assertEqual(sha((ROOT/'proofs/akashlevy-20261009-weighted-numerator/formalization'/r['path']).read_bytes()),r['sha256'])
if __name__=='__main__':unittest.main()
