import argparse
import csv 
from prettytable import PrettyTable, ALL

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Parser for make_table_2.py')
    parser.add_argument('csv_sherwood_quantitative',  type=str, default='',
                        help='Name of the data file for Sherwood quantitative results.')
    parser.add_argument('--csv', type=str, default='',
                        help='Output result in CSV format in the specified file.')

    args = parser.parse_args()

    with open(args.csv_sherwood_quantitative,mode ='r') as dh_sherw_quant, \
         open(args.csv, 'w', newline='') as f:

            # ignore the first row
            next(dh_sherw_quant)

            # read the datafiles with the comma as delimiter
            df_sherw_quant = csv.reader(dh_sherw_quant, delimiter=",")

            # the key list of raw results, as a remainder
            # key_list = ['name', 'k', 'm', 'states', 'supp_size', 'eqs', 'non_trivial_eqs', 'sccs', 'sccsF', 'maxeqs', 'g_size', 'quant_eqs', 'non_trivial_quant_eqs', 'quant_sccs', 'quant_sccsF', 'quant_maxeqs', 'ub_time', 'past_time', 'gg_time', 'quant_OVI_time', 'quant_eqs_time', 'time', 'mem_tot', 'result', 'quant_result']
            header_table_2 = header = ["K", "M", "|f|(quant)", "Time (s)", "Prob"]
            table_2_res = []
            table = PrettyTable()
            table.hrules=ALL
            table.title = 'TABLE 2'
            table.field_names = header_table_2
            for x_line in df_sherw_quant:
                k = x_line[1]
                m = x_line[2]
                quant_eqs = x_line[11]
                time = x_line[21]
                quant_result = x_line[24]
                table_2_res.append([k,m,quant_eqs,time, quant_result])
                table.add_row([k,m,quant_eqs,time, quant_result])

            # printing the table to the terminal
            print(table)

            cw = csv.writer(f)
            cw.writerow(header_table_2)
            cw.writerows(table_2_res)


        