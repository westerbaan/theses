# The index needs xindy rather than makeindex, and where xindy is missing it
# is run in a container instead --- see xindy-container.sh for both reasons.
# The probe is skipped on Windows, where it cannot run and TeX Live does ship
# xindy.  latexmk appends " %O -o %D %S" to a command without a placeholder.
my $xindy = ($^O =~ /^MSWin/ || system('command -v xindy >/dev/null 2>&1') == 0)
                ? "xindy" : "./xindy-container.sh";

$makeindex = "$xindy -M texindy -M parsec  -L general -C utf8";
