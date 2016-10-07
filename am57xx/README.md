Count Reserved
:let n=[-1]| %s/\([A-Za-z0-9_]*\) Reserved Reserved Reserved/\=''.submatch(1).' Reserved'.map(n,'v:val+1')[0].' Reserved'.map(n,'v:val')[0].' Reserved
'.map(n,'v:val')[0]/gc
:%s/[A-Za-z0-9_]* \(([0-9]) \)*\([A-Za-z0-9_.\[\]]*\) \(([0-9]) \)*[A-Za-z0-9_.\[\](),\-\/]* \([A-Za-z0-9_.\[\](),\-\/ ]*\)/\2, \/* \4 *\//gc

:let n=[-1]| %s/RESERVED \([RW]\{1,2\} [0-9]\{2\} 0x[0-9A-Z]\{4\} [A-Z0-9]\{4\} 0x[0-9A-Z]\{4\} [A-Z0-9]\{4\}\)/\='CTRL_CORE_PAD_RESERVED'.map(n, 'v:val+1')[0].' '.submatch(1)/gc

:%s/CTRL_CORE_\([A-Za-z_0-9]*\) [RW]\{1,2\} [0-9]\{2\} 0x[0-9A-Z]\{4\} [A-Z0-9]\{4\} 0x[0-9A-Z]\{4\} \([A-Z0-9]\{4\}\)/#define \1 0x\2/gc
