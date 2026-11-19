# prerequisites
echo "Installing prerequisites and setting up Python virtual environment"
python3 -m venv ./env
source env/bin/activate
pip3 install kaleido joblib plotly numpy tabulate pandas argparse PTable
deactivate