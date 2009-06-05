import os, glob, string
corn_dir = '/data/home/eelis/soft/CoRN'

Rs = [(corn_dir, 'CoRN')]
for f in glob.glob('examples/*'): Rs += [(f, f.split('/')[-1])]
Rs = string.join(map(lambda (x,y): '-R "' + x + '" ' + y, Rs))

coqc = 'coqc ' + Rs

def make_abs(s):
  if s[0] != '/': return Dir("#").abspath + "/" + s
  else: return s

def coq_scan(node, env, path):
  return map(make_abs, os.popen("coqdep -I . " + Rs + " -w " + str(node) + " 2> /dev/null").read().strip().split(' ')[2:])

env = DefaultEnvironment(ENV = os.environ)
env.Append(BUILDERS = {'Coq' : Builder(action = coqc + ' $SOURCE', suffix = '.vo', src_suffix = '.v')})
env.Append(SCANNERS = Scanner(skeys = ['.v'], function = coq_scan))

fs = glob.glob('*.v')
for e in glob.glob('examples/*'): fs += glob.glob(e + '/*.v')
for f in fs: env.Coq(f)
