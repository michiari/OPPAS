#!/usr/bin/env python3

import argparse
import platform
import subprocess
import re
import statistics
import joblib
from mcbench import expand_files
import csv
from tabulate import tabulate

time_pattern = re.compile(r"Total elapsed time: .+ \(([0-9]+\.[0-9]+e[\+\-0-9]+) s\)")
mem_pattern = re.compile(r"Max memory used \(KB\): ([0-9]+)")
result_pattern = re.compile(r"Result:  ((True)|(False))")
#quant_result_pattern = re.compile(r"Result:  (\([0-9]+ % [0-9]+\,[0-9]+ % [0-9]+\))")
quant_result_pattern = re.compile(r"Floating Point Result:  (\(\S+\,\S+\))")
states_pattern = re.compile(r"Input (OPA|pOPA) state count: ([0-9]+)")
supp_pattern = re.compile(r"Support graph size: ([0-9]+)")
eqs_pattern = re.compile(r"Equations solved for termination probabilities: ([0-9]+)")
non_trivial_eqs_pattern = re.compile(r"Non-trivial equations solved for termination probabilities: ([0-9]+)")
sccs_pattern = re.compile(r"SCC count in the support graph: ([0-9]+)")
maxscc_pattern = re.compile(r"Size of the largest SCC in the support graph: ([0-9]+)")
maxeqs_pattern = re.compile(r"Largest number of non trivial equations in an SCC in the Support Graph: ([0-9]+)")

g_size_pattern = re.compile(r"Size of graph G: ([0-9]+)" )

quant_eqs_pattern = re.compile(r"Equations solved for quant mc: ([0-9]+)")
non_trivial_quant_eqs_pattern = re.compile(r"Non-trivial equations solved for quant mc: ([0-9]+)")
quant_sccs_pattern = re.compile(r"SCC count in quant mc weight computation: ([0-9]+)")
quant_maxscc_pattern = re.compile(r"Size of the largest SCC in quant mc weight computation: ([0-9]+)")
quant_maxeqs_pattern = re.compile(r"Largest number of non trivial equations in an SCC in quant mc weight computation: ([0-9]+)")

ub_pattern = re.compile(r"([0-9]+\.[0-9]+e[\+\-0-9]+) s \(upper bounds\)")
past_pattern = re.compile(r"([0-9]+\.[0-9]+e[\+\-0-9]+) s \(PAST certificates\)")
gg_pattern = re.compile(r"([0-9]+\.[0-9]+e[\+\-0-9]+) s \(graph analysis\)")
quant_OVI_pattern = re.compile(r"([0-9]+\.[0-9]+e[\+\-0-9]+) s \(upper bounds with OVI for quant MC\)")
quant_eqs_time_pattern = re.compile(r"([0-9]+\.[0-9]+e[\+\-0-9]+) s \(eq system for quant MC\)")
memgc_pattern = re.compile(r'\("max_bytes_used", "([0-9]+)"\)')
pomc_pattern = re.compile(r".*\.pomc$")

sherwood_pattern = re.compile(r".*sherwood-([0-9]+)\.([0-9]+)\.(\S+).pomc$")
benchmark_pattern = re.compile(r".*/((schelling|tic\-tac\-toe|virus)/\S+).pomc$")

if platform.system() == 'Darwin':
    time_bin = 'gtime'
else:
    time_bin = '/usr/bin/time'

def caps_command(timeout, max_mem):
    if timeout > 0 or max_mem > 0:
        return [
            'systemd-run',
            '--quiet',
            '--user',
            '--scope',
            '-p',
            'KillSignal=SIGKILL',
            '-p',
            'MemoryMax={:d}M'.format(max_mem) if max_mem > 0 else 'MemoryMax=infinity',
            '-p',
            'MemorySwapMax=0' if max_mem > 0 else 'MemorySwapMax=infinity',
            '-p',
            'RuntimeMaxSec={:d}'.format(timeout) if timeout > 0 else 'RuntimeMaxSec=infinity'
        ]
    else:
        return []

def exec_bench(fname, args):
    print('Evaluating file', fname, '...')

    raw_res = subprocess.run(
        caps_command(args.timeout, args.max_mem) +
        [
            time_bin,
            '-f',
            'Max memory used (KB): %M',
            'stack',
            'exec',
            '--',
            'popacheck',
            fname,
            '--stats',
            '+RTS',
            '-t',
            '--machine-readable',
            '-RTS'
        ] + \
        (['--noovi'] if args.noovi else []) + \
        (['--newton'] if args.newton else []),
        capture_output=True
    )
    raw_stdout = raw_res.stdout.decode('utf-8')
    raw_stderr = raw_res.stderr.decode('utf-8')
    raw_out = raw_stdout + raw_stderr
    if args.verbose >= 1:
        print(raw_stdout)
    if args.verbose >= 2:
        print(raw_stderr)

    time_match = time_pattern.search(raw_stdout)
    mem_match = mem_pattern.search(raw_stderr)
    result_match = result_pattern.search(raw_stdout)
    quant_result_match = quant_result_pattern.search(raw_stdout)
    states_match = states_pattern.search(raw_out)
    supp_match = supp_pattern.search(raw_out)
    eqs_match = eqs_pattern.search(raw_out)
    non_trivial_eqs_match = non_trivial_eqs_pattern.search(raw_out)
    sccs_match = sccs_pattern.search(raw_out)
    maxscc_match = maxscc_pattern.search(raw_out)
    maxeqs_match = maxeqs_pattern.search(raw_out)

    g_size_match = g_size_pattern.search(raw_out)

    quant_eqs_match = quant_eqs_pattern.search(raw_out)
    non_trivial_quant_eqs_match = non_trivial_quant_eqs_pattern.search(raw_out)
    quant_sccs_match = quant_sccs_pattern.search(raw_out)
    quant_maxscc_match = quant_maxscc_pattern.search(raw_out)
    quant_maxeqs_match = quant_maxeqs_pattern.search(raw_out)
    
    ub_match = ub_pattern.search(raw_out)
    past_match = past_pattern.search(raw_out)
    gg_match = gg_pattern.search(raw_stdout)
    quant_OVI_match = quant_OVI_pattern.search(raw_out)
    quant_eqs_time_match = quant_eqs_time_pattern.search(raw_out)
    memgc_match = memgc_pattern.search(raw_stderr)

    sherwood_match = sherwood_pattern.search(fname)
    benchmark_match = benchmark_pattern.search(fname)
    check_match = lambda m, groupno=1, err=-1: m.group(groupno) if m else err
    record = {
        'name': str(check_match(sherwood_match,3, check_match(benchmark_match,1,fname))),
        'time': float(check_match(time_match)),
        'ub_time': float(check_match(ub_match)),
        'past_time': float(check_match(past_match)),
        'gg_time': float(check_match(gg_match)),
        'mem_tot': int(check_match(mem_match)),
        'mem_gc': int(check_match(memgc_match, 1, -2**10)),
        'states': int(check_match(states_match, 2)),
        'supp_size': int(check_match(supp_match)),
        'eqs': int(check_match(eqs_match)),
        'non_trivial_eqs': int(check_match(non_trivial_eqs_match)),
        'sccs': int(check_match(sccs_match)),
        'maxscc': int(check_match(maxscc_match)),
        'maxeqs': int(check_match(maxeqs_match)),
        'g_size': int(check_match(g_size_match)),
        'quant_eqs': int(check_match(quant_eqs_match)),
        'non_trivial_quant_eqs': int(check_match(non_trivial_quant_eqs_match)),
        'quant_sccs': int(check_match(quant_sccs_match)),
        'quant_maxscc': int(check_match(quant_maxscc_match)),
        'quant_maxeqs': int(check_match(quant_maxeqs_match)),
        'quant_OVI_time': float(check_match(quant_OVI_match)),
        'quant_eqs_time': float(check_match(quant_eqs_time_match)),
        'k' : int(check_match(sherwood_match)),
        'm' : int(check_match(sherwood_match, 2)),
    }
    if raw_res.returncode != 0:
        if raw_res.returncode == -9:
            return record | { 'result': 'TO', 'quant_result': 'TO'}
        elif raw_res.returncode in [135,137,139]:
            return record | { 'result': 'OOM', 'quant_result': 'OOM'}
        return record | { 'result': 'Error {:d}'.format(raw_res.returncode),  'quant_result': '-' }
    return record | { 'result': check_match(result_match),  'quant_result': check_match(quant_result_match) }

def iter_bench(fname, args):
    get_column = lambda rows, i: [r[i] for r in rows]
    results = [exec_bench(fname, args) for _ in range(0, args.iters)]
    return {
        'name': results[0]['name'],
        'k' : results[0]['k'],
        'm' : results[0]['m'],
        'time': statistics.mean(get_column(results, 'time')),
        'ub_time': statistics.mean(get_column(results, 'ub_time')),
        'past_time': statistics.mean(get_column(results, 'past_time')),
        'gg_time': statistics.mean(get_column(results, 'gg_time')),
        'quant_OVI_time' : statistics.mean(get_column(results, 'quant_OVI_time')),
        'quant_eqs_time' : statistics.mean(get_column(results, 'quant_eqs_time')),
        'mem_tot': statistics.mean(get_column(results, 'mem_tot')),
        'mem_gc': statistics.mean(get_column(results, 'mem_gc'))/(2**10),
        'result': results[0]['result'],
        'quant_result': results[0]['quant_result'],
        'states': results[0]['states'],
        'supp_size': results[0]['supp_size'],
        'eqs': results[0]['eqs'],
        'non_trivial_eqs': results[0]['non_trivial_eqs'],
        'sccs': results[0]['sccs'],
        'maxscc': results[0]['maxscc'],
        'maxeqs': results[0]['maxeqs'],
        'g_size': results[0]['g_size'],        
        'quant_eqs': results[0]['quant_eqs'],
        'non_trivial_quant_eqs': results[0]['non_trivial_quant_eqs'],
        'quant_sccs': results[0]['quant_sccs'],
        'quant_maxscc': results[0]['quant_maxscc'],
        'quant_maxeqs': results[0]['quant_maxeqs'],
    }

def exec_all(fnames, args):
    if args.jobs <= 1:
        return [iter_bench(fname, args) for fname in fnames]
    else:
        return joblib.Parallel(n_jobs=args.jobs)(joblib.delayed(iter_bench)(fname, args)
                                                 for fname in fnames)
def to_list(results, key_map_list):
    return [[mapf(r[key]) for key, mapf in key_map_list] for r in results]

if __name__ == '__main__':
    argp = argparse.ArgumentParser()
    argp.add_argument('-o', '--noovi', action='store_true', help='Use z3 instead of OVI to compute upper bounds')
    argp.add_argument('-n', '--newton', action='store_true', help='Use Newton method for iterating fixpoint equations')
    argp.add_argument('-i', '--iters', type=int, default=1, help='Number of executions for each benchmark')
    argp.add_argument('-j', '--jobs', type=int, default=1, help='Maximum number of benchmarks to execute in parallel')
    argp.add_argument('-t', '--timeout', type=int, default=0, help='Timeout in seconds for each benchmark. 0 = no timeout (default)')
    argp.add_argument('-M', '--max_mem', type=int, default=0, help='Maximum memory to be allocated in MiBs. 0 = no limit (default)')
    argp.add_argument('-v', '--verbose', action='count', default=0, help='Show individual benchmark results')
    argp.add_argument('--raw_csv', type=str, default='', help='Output result in CSV format in the specified file')
    argp.add_argument('--print', action='store_true', help='Print results to the terminal.')
    argp.add_argument('benchmarks', type=str, nargs='+', help='*.pomc files or directories containing them')
    args = argp.parse_args()

    print(f'Running benchmarks...')
    results = exec_all(expand_files(args.benchmarks), args)

    key_list = ['name', 'k', 'm', 'states', 'supp_size', 'eqs', 'non_trivial_eqs', 'sccs', 'maxscc', 'maxeqs', 'g_size', 'quant_eqs', 'non_trivial_quant_eqs', 'quant_sccs', 'quant_maxscc', 'quant_maxeqs', 'ub_time', 'past_time', 'gg_time', 'quant_OVI_time', 'quant_eqs_time', 'time', 'mem_tot', 'result', 'quant_result']
    results_matrix = to_list(results, list(map(lambda k: (k,  lambda x: x), key_list)))
    header = ["Name", "Array_values_bits(K)", "Array_length(M)", "|Q_A|", "|SG|", "|f|", "|f_NT|", "#SCC", "|SCC|max", "|f(SCC)_NT|max", "|G|", "|f|(quant)", "|f_NT|(quant)", "#SCC(quant)", "|SCC|max(quant)", "|f(SCC)_NT|max(quant)", "UB Time (s)", "PAST Time (s)", "G Time (s)", "quant OVI (s)", "quant Eqs (s)", "Time (s)", "Memory (KiB)", "Holds AS", "Prob"]

    # store raw results somewhere
    if args.raw_csv:
        with open(args.raw_csv, 'w', newline='') as f:
            cw = csv.writer(f)
            cw.writerow(header)
            cw.writerows(results_matrix)

    if args.print:
        print(tabulate(results_matrix, headers=header))
    if not args.raw_csv and not args.print:
        print("Benchmarks executed correctly, no place to print them specified. Exiting...")
