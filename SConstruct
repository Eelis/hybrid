import os, glob, string
libs = os.environ["COQLIBS"]
coqtop = os.environ["COQTOP"]
corn_dir = libs + '/CoRN'
color_dir = libs + '/color/color/trunk/color'

Rs = [(corn_dir, 'CoRN'), (color_dir, 'CoLoR'), ('.', 'hybrid')]
Rs = string.join(map(lambda (x,y): '-R "' + x + '" ' + y, Rs))

coqc = coqtop + '/bin/coqc -noglob ' + Rs

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
