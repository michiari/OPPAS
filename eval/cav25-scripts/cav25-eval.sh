#!/bin/bash

# default options
timeout=3600 # (s)
maxMem=30000 # (MB)
jobs=1
iters=1

smoke_test=false

# Get the options
while getopts "st:m:j:i:" option; do
   case $option in
      t) timeout=$OPTARG;;
      m) maxMem=$OPTARG;;
      j) jobs=$OPTARG;;
      i) iters=$OPTARG;;
      s) smoke_test=true;;
     \?) echo "Error: Invalid option"
         exit;;
   esac
done

echo "Timeout: ${timeout} s"
echo "maxMem: ${maxMem} MB"
echo "Smoke Test: ${smoke_test}"
echo "Jobs in parallel: ${jobs}"
echo "Number of iterations per test: ${iters}"


pomc_folder="OPPAS"
cd $pomc_folder

# creating results folder (removing old ones if they already exist)
eval_folder="eval"
results_dir="../POPACheck-results"
raw_results_dir="${results_dir}/raw-results"
if [ -d $results_dir ]; then rm -rf $results_dir; fi
mkdir -p $results_dir
mkdir -p $raw_results_dir

echo "Activating Python env..."
source ../env/bin/activate

# Fig. 8
sherwood_nr_states_raw_results="../precomputed-results/sherwood_nr_states.csv"
sherwood_qual_raw_results="${raw_results_dir}/sherwood_qual.csv"
if [ "$smoke_test" = true ]; then 
   echo "Running Sherwood qualitative model checking only for formula S1 (smoke test)..."
   python3 "${eval_folder}/probbench.py" "${eval_folder}/prob/Sherwood/benchmark/qualitative/S1" -t ${timeout} -M ${maxMem} --raw_csv ${sherwood_qual_raw_results} -j ${jobs} -i ${iters}
else 
   echo "Running Sherwood qualitative model checking..."
   python3 "${eval_folder}/probbench.py" "${eval_folder}/prob/Sherwood/benchmark/qualitative" -t ${timeout} -M ${maxMem} --raw_csv ${sherwood_qual_raw_results} -j ${jobs} -i ${iters}
fi
echo "Generating scatter plot (Fig.8)"
python3 ../make_qual_scatter_plot.py "${sherwood_qual_raw_results}" "${sherwood_nr_states_raw_results}" ${timeout} -o "${results_dir}/Figure-8"

# Table 2
echo "Running Sherwood quantitative model checking..."
sherwood_quant_results="${results_dir}/table_2.csv"
sherwood_quant_raw_results="${raw_results_dir}/sherwood_quant.csv"
python3 "${eval_folder}/probbench.py" "${eval_folder}/prob/Sherwood/benchmark/quantitative" -t ${timeout} -M ${maxMem} --raw_csv ${sherwood_quant_raw_results} -j ${jobs} -i ${iters}
echo "Generating Table 2..."
python3 ../make_table_2.py "${sherwood_quant_raw_results}" --csv ${sherwood_quant_results}

# Table 3
echo "Running Schelling, Tic-Tac-Toe and Virus experiments - termination probabilities via OVI"
benchmark_term_ovi_raw_results="${raw_results_dir}/benchmark_termination_OVI.csv"
python3 "${eval_folder}/probbench.py" "${eval_folder}/prob/established/approximate" -t ${timeout} -M ${maxMem} --raw_csv ${benchmark_term_ovi_raw_results} -j ${jobs} -i ${iters}
echo "Running Schelling, Tic-Tac-Toe and Virus experiments - termination probabilities via Z3"
benchmark_term_z3_raw_results="${raw_results_dir}/benchmark_termination_Z3.csv"
python3 "${eval_folder}/probbench.py" "${eval_folder}/prob/established/approximate" --noovi -t ${timeout} -M ${maxMem} --raw_csv ${benchmark_term_z3_raw_results} -j ${jobs} -i ${iters}
echo "Generating Table 3..."
benchmark_term_result="${results_dir}/table_3.csv"
python3 ../make_table_3.py "${benchmark_term_ovi_raw_results}" "${benchmark_term_z3_raw_results}" --csv "${benchmark_term_result}"

# Table 4
echo "Running Schelling, Tic-Tac-Toe and Virus experiments - qualitative model checking"
benchmark_qual_raw_results="${raw_results_dir}/benchmark_qualitative.csv"
python3 "${eval_folder}/probbench.py" "${eval_folder}/prob/established/qualitative" -t ${timeout} -M ${maxMem} --raw_csv ${benchmark_qual_raw_results} -j ${jobs} -i ${iters}
echo "Running Schelling, Tic-Tac-Toe and Virus experiments - quantitative model checking"
benchmark_quant_raw_results="${raw_results_dir}/benchmark_quantitative.csv"
python3 "${eval_folder}/probbench.py" "${eval_folder}/prob/established/quantitative" -t ${timeout} -M ${maxMem} --raw_csv ${benchmark_quant_raw_results} -j ${jobs} -i ${iters}
echo "Generating Table 4..."
benchmark_mc_result="${results_dir}/table_4.csv"
python3 ../make_table_4.py "${benchmark_qual_raw_results}" "${benchmark_quant_raw_results}" --csv "${benchmark_mc_result}"

echo "Script terminated, deactivating virtual environment"
deactivate
