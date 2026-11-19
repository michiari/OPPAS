import argparse
import csv 
from prettytable import PrettyTable, ALL

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Parser for make_table_3.py')
    parser.add_argument('csv_terminaton_ovi',  type=str, default='',
                        help='Name of the data file for OVI termination results of established benchmarks.')
    parser.add_argument('csv_terminaton_z3',  type=str, default='',
                        help='Name of the data file for Z3 termination results of established benchmarks.')
    parser.add_argument('--csv', type=str, default='',
                        help='Output result in CSV format in the specified file.')

    args = parser.parse_args()

    with open(args.csv_terminaton_ovi,mode ='r') as dh_term_ovi, \
         open(args.csv_terminaton_z3,mode ='r') as dh_term_z3, \
         open(args.csv, 'w', newline='') as f:

            # ignore the first row
            next(dh_term_ovi)
            next(dh_term_z3)

            # read the datafiles with the comma as delimiter
            df_ovi = csv.reader(dh_term_ovi, delimiter=",")
            df_z3 = csv.reader(dh_term_z3, delimiter=",")

            table_3_res = []
            # the key list of raw results, as a remainder
            # key_list = ['name', 'k', 'm', 'states', 'supp_size', 'eqs', 'non_trivial_eqs', 'sccs', 'sccsF', 'maxeqs', 'g_size', 'quant_eqs', 'non_trivial_quant_eqs', 'quant_sccs', 'quant_sccsF', 'quant_maxeqs', 'ub_time', 'past_time', 'gg_time', 'quant_OVI_time', 'quant_eqs_time', 'time', 'mem_tot', 'result', 'quant_result']
            header_table_3 = ["name", "|Q|", "|f|", "|f_NT|", "|f(SCC)_NT|max", "time_Z3 (s)", "time_OVI (s)", "t_PAST"]
            table = PrettyTable()
            table.hrules=ALL
            table.title = 'TABLE 3'
            table.field_names = header_table_3
            for (ovi_res, z3_res) in zip(df_ovi, df_z3):
                name = ovi_res[0]
                states = ovi_res[3]
                eqs = ovi_res[5]
                non_trivial_eqs = ovi_res[6]
                maxeqs = ovi_res[9]
                z3_time = z3_res[16]
                if z3_res[23] == 'TO':
                    z3_time = 'TO'
                elif z3_res[23] == 'OOM':
                    z3_time = 'OOM'
                elif float(z3_time) < 0:
                    z3_time = "TO"

                ovi_time = ovi_res[16]
                if ovi_res[23] == 'TO':
                    ovi_time = 'TO'
                elif ovi_res[23] == 'OOM':
                    ovi_time = 'OOM'
                elif float(ovi_time) < 0:
                    ovi_time = "TO"
                past_time = ovi_res[17]
                table_3_res.append([name,states, eqs, non_trivial_eqs, maxeqs, z3_time, ovi_time, past_time])
                table.add_row([name,states, eqs, non_trivial_eqs, maxeqs, z3_time, ovi_time, past_time])


            print(table)
            cw = csv.writer(f)
            cw.writerow(header_table_3)
            cw.writerows(table_3_res)
            