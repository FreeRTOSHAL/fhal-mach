Count Reserved
:let n=[-1]| %s/\([A-Za-z0-9_]*\) Reserved Reserved Reserved/\=''.submatch(1).' Reserved'.map(n,'v:val+1')[0].' Reserved'.map(n,'v:val')[0].' Reserved
'.map(n,'v:val')[0]/gc
:%s/[A-Za-z0-9_]* \(([0-9]) \)*\([A-Za-z0-9_.\[\]]*\) \(([0-9]) \)*[A-Za-z0-9_.\[\](),\-\/]* \([A-Za-z0-9_.\[\](),\-\/ ]*\)/\2, \/* \4 *\//gc
