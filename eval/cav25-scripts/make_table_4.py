import argparse
import csv 
from prettytable import PrettyTable, ALL

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Parser for make_table_4.py')
    parser.add_argument('csv_qualitative',  type=str, default='',
                        help='Name of the data file for qualitative model checking results of established benchmarks.')
    parser.add_argument('csv_quantitative',  type=str, default='',
                        help='Name of the data file for quantitative model checking results of established benchmarks.')
    parser.add_argument('--csv', type=str, default='',
                        help='Output result in CSV format in the specified file.')

    args = parser.parse_args()

    with open(args.csv_qualitative, mode ='r') as dh_qual, \
         open(args.csv, 'w', newline='') as f:

            # ignore the first row
            next(dh_qual)
            

            # read the datafiles with the comma as delimiter
            df_qual = csv.reader(dh_qual, delimiter=",")

            table_4_res = []
            # the key list of raw results, as a remainder
            # key_list = ['name', 'k', 'm', 'states', 'supp_size', 'eqs', 'non_trivial_eqs', 'sccs', 'sccsF', 'maxeqs', 'g_size', 'quant_eqs', 'non_trivial_quant_eqs', 'quant_sccs', 'quant_sccsF', 'quant_maxeqs', 'ub_time', 'past_time', 'gg_time', 'quant_OVI_time', 'quant_eqs_time', 'time', 'mem_tot', 'result', 'quant_result']
            header_table_4 = ["name", "G Time (s)", "Total Qual Time (s)", "Holds AS", "|f|(quant)", "|f_NT|(quant)", "|scc_f|max(quant)", "quant OVI time (s)", "Total Quant Time (s)", "Prob"]
            table = PrettyTable()
            table.hrules=ALL
            table.title = 'TABLE 4'
            table.field_names = header_table_4
            for qual_line in df_qual:
                name = qual_line[0]
                g_time = qual_line[18]
                qual_time = qual_line[21]
                almost_sure = qual_line[23]

                quant_eqs = "-"
                non_trivial_quant_eqs = "-"
                quant_maxeqs = "-"
                quant_OVI = "-"
                quant_time = "-"
                quant_result = "1" if almost_sure == "True" else almost_sure
                
                with open(args.csv_quantitative,mode ='r') as dh_quant:
                    next(dh_quant)
                    df_quant = csv.reader(dh_quant, delimiter=",")
                    
                    for quant_line in df_quant:
                        if quant_line[0] == name:
                            # replace quantitative results
                            quant_eqs = quant_line[11]
                            non_trivial_quant_eqs = quant_line[12]
                            quant_maxeqs = quant_line[15]
                            quant_OVI = quant_line[19]
                            quant_time = quant_line[21]
                            quant_result = quant_line[24]

                table_4_res.append([name, g_time, qual_time, almost_sure, quant_eqs, non_trivial_quant_eqs, quant_maxeqs, quant_OVI, quant_time, quant_result])
                table.add_row([name, g_time, qual_time, almost_sure, quant_eqs, non_trivial_quant_eqs, quant_maxeqs, quant_OVI, quant_time, quant_result])
                
            print(table)
            
            cw = csv.writer(f)
            cw.writerow(header_table_4)
            cw.writerows(table_4_res)
            
            
                
            
                        

                  
                
                  
            


            




