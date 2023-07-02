#!/bin/bash
uniq_str="exp_"`date +%H%M%S%d%m%Y`
#modify this path to some directory where you want to store the log and result files
export LOG_PATH="/tmp/$uniq_str"
#modify this to set timeout for each task
export TIMEOUT="200s"
#modify this to maximum number of parallel jobs that you can run
export PARALLEL_JOBS=4

#modify this to the path of MaxPrANQ
export MAXPRANQ_BIN=$(pwd)"/build/tools/nonlin/maxpranq "
export BIN=$MAXPRANQ_BIN" --max ";
export FAILED_FILES=$LOG_PATH"/failed_files"
export TIMING_FILE=$LOG_PATH"/timings"
export IND_PATH=$LOG_PATH"/output"
export TMPFILE=`mktemp` || exit 1
export TMPFILE="bench_precondn/fmcad_bench/fmcad_bench"
export CURFILEVAL=`mktemp` || exit 1
export FAILEDFILEVAL=`mktemp` || exit 1
export MAYNOTBEMAXIMAL_FILES=$LOG_PATH"/maynotbemaximal_files"
export MAYNOTBEMAXIMALFILEVAL=`mktemp` || exit 1
export ENC_PATH=$LOG_PATH"/encodings/"
export OVERALL_RESULT_FILE=$LOG_PATH"/overall.csv"
export OVERALL_RESULT_FILE_SORTED=$LOG_PATH"/overall_sorted.csv"
export OVERALL_STATUS_FILE=$LOG_PATH"/overall_status.csv"
export OVERALL_MD=$LOG_PATH"/last_commit_result.md"
export RUN_MAX=1


mkdir $LOG_PATH
mkdir $IND_PATH
mkdir $ENC_PATH

function count_file_lines()
{
    if [ -s $1 ]
    then
	echo -n `wc -l $1 | cut -d' ' -f1`
    else
	echo -n "0"
    fi
}

function parallel_runall()
{
    inputfile=$1
    outputfile=$(basename "$inputfile")
    outputfile="${outputfile%.*}"
    
    terminaloutput=$IND_PATH"/tty_"${outputfile}
    timeoutput=$IND_PATH"/time_"${outputfile}
    exitoutput=$IND_PATH"/exit_"${outputfile}

    encprefix=$outputfile
    
    rm "/tmp/"$encprefix* 2>/dev/null
    
    outputfile=$LOG_PATH"/"${outputfile}"_out.smt2"

    starttime=$(date +%s%N)
    
    timeout -k 10 $TIMEOUT $BIN $inputfile > $terminaloutput
    exit_status=$?

    endtime=$(date +%s%N)

    #sleep for a random float time between [0,2)
    sleep `printf "%d.%d" $((RANDOM%2)) $RANDOM`

    mv "/tmp/"$encprefix* $ENC_PATH 2>/dev/null

    maynotbemaximalcount=`cat $MAYNOTBEMAXIMALFILEVAL`
    failedfilecount=`cat $FAILEDFILEVAL`

    if [ "$RUN_MAX" -eq "0" ]; then
        
        if grep -q "unsat" $terminaloutput; then
            t=$(((endtime - starttime)/1000000))
            echo $t > $timeoutput
            inputfiledir=$(dirname "$inputfile")
            echo $(basename "$inputfiledir")"/"$(basename "$inputfile")",PASS,"$t >> $OVERALL_RESULT_FILE
        else 
            failedfilecount=$((failedfilecount+1))
            echo -n $failedfilecount > $FAILEDFILEVAL
            echo $inputfile","$exit_status",TO" >> $FAILED_FILES
            inputfiledir=$(dirname "$inputfile")
            echo $(basename "$inputfiledir")"/"$(basename "$inputfile")",FAIL,"$exit_status >> $OVERALL_RESULT_FILE

        fi
        
    else
        t=$(((endtime - starttime)/1000000))
        if grep -q "may not be maximal" $terminaloutput; then	
            maynotbemaximalcount=$((maynotbemaximalcount+1))
            echo -n $maynotbemaximalcount > $MAYNOTBEMAXIMALFILEVAL
            echo $inputfile","$exit_status",mnb" >> $MAYNOTBEMAXIMAL_FILES
            inputfiledir=$(dirname "$inputfile")
            echo $(basename "$inputfiledir")"/"$(basename "$inputfile")",FAIL,"$t >> $OVERALL_RESULT_FILE
        elif grep -q "maximal" $terminaloutput; then
            echo $t > $timeoutput
            inputfiledir=$(dirname "$inputfile")
            echo $(basename "$inputfiledir")"/"$(basename "$inputfile")",PASS,"$t >> $OVERALL_RESULT_FILE
        else 
            failedfilecount=$((failedfilecount+1))
            echo -n $failedfilecount > $FAILEDFILEVAL
            echo $inputfile","$exit_status",TO" >> $FAILED_FILES
            inputfiledir=$(dirname "$inputfile")
            echo $(basename "$inputfiledir")"/"$(basename "$inputfile")",FAIL,"$t >> $OVERALL_RESULT_FILE

        fi

    fi
    
    curfilecount=`cat $CURFILEVAL`
    curfilecount=$((curfilecount + 1))
    echo -n $curfilecount > $CURFILEVAL
    if [ "$RUN_MAX" -eq "0" ]; then
        echo  -ne "completed: $curfilecount/$totalfiles (failed: $failedfilecount)\r"
    else
        echo  -ne "completed: $curfilecount/$totalfiles (failed: $failedfilecount, mnbm: $maynotbemaximalcount)\r"                
    fi
    
}

export -f parallel_runall

export totalfiles=`count_file_lines $TMPFILE` 
export curfilecount=0
export failedfilecount=0
export maynotbemaximalcount=0

echo "Benchmark,Result,Time (in ms) or Exit Status" > $OVERALL_RESULT_FILE

cat $TMPFILE | xargs -n 1 -P $PARALLEL_JOBS -I {} bash -c 'parallel_runall "{}"'

for tfile in `ls $IND_PATH"/time_"*`;
do
    tfile_base=$(basename "$tfile")
    echo -n ${tfile_base#*_}"," >> $TIMING_FILE
    cat $tfile >> $TIMING_FILE
#    echo $BIN >> $TIMING_FILE
done

echo
echo "Total files: "$totalfiles
if [ "$RUN_MAX" -eq "0" ]; then
    echo "TO: "`count_file_lines $FAILED_FILES`
else
    echo "Maximal: "`count_file_lines $TIMING_FILE`
    echo "May not be maximal: "`count_file_lines $MAYNOTBEMAXIMAL_FILES`
fi
echo "logpath:$LOG_PATH"
