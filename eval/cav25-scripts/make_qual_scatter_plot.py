import os, os.path, sys, argparse
import csv 
import plotly.express as px
import plotly.graph_objects as go
import pandas as pd
import numpy as np
import plotly.io as pio
#pio.kaleido.scope.mathjax = None
import warnings


def add_timeout_lines(fig, args):
    ### Add timeout lines for XTOOL
    x_timeoutline = np.arange(100,500000)
    y_timeoutline = [args.timeout] * 500000
    fig.add_trace(go.Scatter(
        x=x_timeoutline,
        y=y_timeoutline,
        mode='lines',
        name='Timeout line',
        showlegend=True,
        line=dict(
            color="blue",
            width=1
        )
    ))

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Parser for make_scatter_plot.py')
    parser.add_argument('csv_times',  type=str, default='',
                        help='Name of the data file for the time results.')
    parser.add_argument('csv_nr_states',  type=str, default='',
                        help='Name of the data file for the number of states.')
    parser.add_argument('timeout', metavar='timeout', type=int,
                        default=0,
                        help='Time value for the timeout.')
    parser.add_argument('-o', '--output',  type=str, default='',
                        help='Name of the output file (without format)')

    args = parser.parse_args()

    # Create lists for data
    xtool_result_list = []
    xtool_parameter = []
    formula_list = []
    nr_states_dict = {}

    with open(args.csv_nr_states,mode ='r') as dh:
        # ignore the first row
        next(dh)

        # read the datafile with the comma as delimiter
        df1 = csv.reader(dh, delimiter=",")

        # the key list of raw results, as a remainder
        # key_list = ['name', 'k', 'm', 'states', 'supp_size', 'eqs', 'non_trivial_eqs', 'sccs', 'sccsF', 'maxeqs', 'g_size', 'quant_eqs', 'non_trivial_quant_eqs', 'quant_sccs', 'quant_sccsF', 'quant_maxeqs', 'ub_time', 'past_time', 'gg_time', 'quant_OVI_time', 'quant_eqs_time', 'time', 'mem_tot', 'result', 'quant_result']
            
        # read the content of the datafile 
        for x_line in df1:
            k = int(x_line[1])
            m = int(x_line[2])
            nr_states = int(x_line[3])
            if nr_states < 0:
                warnings.warn(f"Could not collect number of states for model with K = {k}, M = {m}, setting default to 100'000. Please increase time and memory limits.")
            nr_states_dict[(k,m)] = nr_states if nr_states > 0 else 100000 

    # opening the csv file for xtool
    with open(args.csv_times,mode ='r') as dh1:
        # ignore the first row
        next(dh1)

        # read the datafile with the comma as delimiter
        df1 = csv.reader(dh1, delimiter=",")

        # read the content of the datafile 
        for x_line in df1:
            # take the line and remove empty elements
            x_line = [el for el in x_line if el!='']

            ### RESULT (time)
            # take the value of the result of xtool
            result_xtool = float(x_line[21].strip())
            formula = x_line[0].strip()

            if result_xtool == -1:
                result_xtool = float(args.timeout)

            xtool_result_list.append(result_xtool)
            formula_list.append(formula)

            ### NR States
            k = int(x_line[1])
            m = int(x_line[2])
            nr_states = nr_states_dict[(k,m)]

            xtool_parameter.append(nr_states)


            # create dictionary for the data
    data = {'result'     : xtool_result_list,
            'parameter'  : xtool_parameter,
            'formula'   : formula_list
           }
    # create pandas dataframe
    df_measure = pd.DataFrame(data)

    # draw the plot
    fig = px.scatter(
            df_measure, 
            x=      "parameter",
            y=      "result",
            color=  "formula",
            symbol=  "formula",
            labels={"parameter":    "pOPA states",
                    "result":    "Time (sec)",
                    "formula":  "Formula"
                   },
            color_discrete_sequence=px.colors.qualitative.D3
            #title="Title"
        )

    # set the same scale of both axis

    fig.update_yaxes(type="log")
    fig.update_xaxes(type="log")
    #fig.update_yaxes(
    #    scaleanchor="x",
    #    scaleratio=1,
    #  )

    # set the ranges for x axis
    #fig.update_xaxes(range=[-1,np.log10(args.errortime*2)])
    fig.update_xaxes(linecolor='black', gridcolor='lightgrey', griddash='dot', title_standoff=5)

    # set the ranges of y axis
    fig.update_yaxes(range=[-1,np.log10(args.timeout*1.1)], linecolor='black', gridcolor='lightgrey', griddash='dot', title_standoff=5)

    add_timeout_lines(fig,args)


    # styling the marker
    fig.update_traces(
        marker=dict(
               #symbol='x',
               size=6,
               #color='gray'
           ),
        )

    # Layout
    layout = dict(
        showlegend = True,
        font_family='"Latin Modern Math", "Times New Roman", serif',
        plot_bgcolor='white',
        margin_b = 0,
        margin_t = 0,
        margin_l = 0,
        margin_r = 0,
        width = 400,
        height = 300
    )
    fig.update(layout = layout)
    legend = dict(
        orientation="h",
        yanchor="bottom",
        y=1.02,
        xanchor="right",
        x=1
    )
    fig.update_layout(legend=legend)

    # create/show the fig
    fig.write_image(args.output+".pdf", format='pdf')
    fig.write_image(args.output+".png", format='png')

