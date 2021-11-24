rm -rf mesured-time
mkdir mesured-time
time for run in {1..10}; do
    rm -rf lib fstar/out rust/target rust/include generated_src/extern.h 
    time (make -C fstar &> /dev/null) 2>> mesured-time/fstar-verify.log;
    cd misraC-Checker
    time (python3 main.py `ls ../misrac/*.c` &> /dev/null) 2>> ../mesured-time/misrac-check.log;
    cd ..
    time (make -f Makefile.compile &> /dev/null) 2>> mesured-time/compile.log;
done 2> mesured-time/all.log
