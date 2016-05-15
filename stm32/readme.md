gen ISR array:
:%s/  \([A-Za-z_0-9]*\)[ ]*= [0-9].*\(\/\*.*\*\/\)/[\1] = \L\1\E, \2/gc
gen ISR function:
:%s/  \([A-Za-z_0-9]*\)[ ]*= [0-9].*\(\/\*.*\*\/\)/void WEAK ALIAS(dummy_handler) \L\1\E(void); \2/gc
remove spaces
:%s/\(\/\*!< [A-Za-z0-9,&() ]*[A-Za-z0-9,&()]\)  [ ]*\*\//\1 *\//gc
