:%s/[ ]*\.long[ ]*\([A-Za-z_0-9]*\)[ ]*\(\/\*[ A-Za-z_\-\/.0-9\[\]:,()&]*\*\/\)/void WEAK ALIAS(dummy_handler) \1(void); \2/gc
:%s/[ ]*\.long[ ]*\([A-Za-z_0-9]*\)[ ]*\(\/\*[ A-Za-z_\-\/.0-9\[\]:,()&]*\*\/\)/void \1(void); \2/gc
:let n=[-1]| %s/[ ]*\.long[ ]*\([A-Za-z_0-9]*\)[ ]*\(\/\*[ A-Za-z_\-\/.0-9\[\]:,()&]*\*\/\)/\='#define NVIC_'.submatch(1).' '.map(n, 'v:val+1')[0].' '
.submatch(2)/g
:%s/#define \([A-Z-A-z0-9_]*\)/#define \U\1\E/g
:%s/[ ]*\.long[ ]*\([A-Za-z_0-9]*\)[ ]*\(\/\*[ A-Za-z_\-\/.0-9\[\]:,()]*\*\/\)/[NVIC_\U\1\E] = \1, \2/gc
