import os, glob, string
corn_dir = '~/coq_libs/CoRN'
coqc = 'coqc -R ' + corn_dir + ' CoRN'
env = DefaultEnvironment(ENV = os.environ)
env.Append(BUILDERS = {'Coq' : Builder(action = coqc + ' $SOURCE', suffix = '.vo', src_suffix = '.v')})
env.Append(SCANNERS = Scanner(skeys = ['.v'], function = coq_scan))

fs = glob.glob('*.v')
for e in glob.glob('examples/*'): fs += glob.glob(e + '/*.v')
for f in fs: env.Coq(f)
