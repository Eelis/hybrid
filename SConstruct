import os, glob
corn_dir = '/data/home/eelis/soft/CoRN'
coqc = 'coqc -R ' + corn_dir + ' CoRN'
env = DefaultEnvironment(ENV = os.environ)
env.Append(BUILDERS = {'Coq' : Builder(action = coqc + ' $SOURCE', suffix = '.vo', src_suffix = '.v')})
env.Append(SCANNERS = Scanner(skeys = ['.v'], function = (lambda node, env, path: os.popen("coqdep -R " + corn_dir + " CoRN -w -I . " + str(node)).read().strip().split(' ')[2:])))

fs = glob.glob('*.v')
for f in fs: env.Coq(f)
