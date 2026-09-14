import pathlib,json,hashlib,tempfile,subprocess,sys
root=pathlib.Path.cwd(); own=root/'Research/UnforcedRestart/Round4/PeriodizationTransport'
r=json.loads((root/'Research/UnforcedRestart/Round4/Integration/strict-u8436kce/receipt.json').read_text())
for p,h in r['inputs'].items():
 assert hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()==h,p
out=pathlib.Path(tempfile.mkdtemp(prefix='strict-',dir=own)); (out/'home').mkdir()
src=own/(sys.argv[1] if len(sys.argv)>1 else 'Cell.lean')
env=r['environment'].copy();env['HOME']=str(out/'home');env['LEAN_PATH']=r['lib']+':'+env['LEAN_PATH']
cmd=r['command'][:]; j=cmd.index('env'); cmd=cmd[:j]+['env','-i']+[k+'='+v for k,v in env.items()]+[r['command'][r['command'].index('-j1')-1],'-j1','-DautoImplicit=false','-DwarningAsError=true','-o',str(out/'Cell.olean'),'-i',str(out/'Cell.ilean'),str(src.relative_to(root))]
p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(out/'compile.log').write_bytes(p.stdout)
data={'source':str(src.relative_to(root)),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'command':cmd,'exit':p.returncode,'inherited_receipt':r,'outputs':{str(x):hashlib.sha256(x.read_bytes()).hexdigest() for x in out.iterdir() if x.is_file()}}
(out/'receipt.json').write_text(json.dumps(data,indent=2));print(out);print(p.stdout.decode());sys.exit(p.returncode)
