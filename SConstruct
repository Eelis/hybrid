import os, glob
coqc = '/home/gi/cek/trunk/bin/coqc -R /home/gi/cek/CoRN CoRN '
env = DefaultEnvironment(ENV = os.environ)
env.Append(BUILDERS = {'Coq' : Builder(action = coqc + '$SOURCE', suffix = '.vo', src_suffix = '.v')})
env.Append(SCANNERS = Scanner(skeys = ['.v'], function = (lambda node, env, path: os.popen("coqdep -R /home/gi/cek/CoRN -w -I . " + str(node)).read().strip().split(' ')[2:])))

fs = glob.glob('*.v')
for f in fs: env.Coq(f)

