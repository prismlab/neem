import subprocess
import time
from tabulate import tabulate

# Function to execute command and measure time
def execute_command(command):
    start_time = time.time()
    try:
        subprocess.run(command, shell=True, check=True)
        #stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError as e:
        print(f"Error executing the command: {e}")
        return None
    end_time = time.time()
    elapsed_time = end_time - start_time
    return elapsed_time

# List of commands to execute
commands = [
	"fstar.exe mrdts-new/Increment-only_counter/App_new.fst interface/App_new.fsti",
	"fstar.exe mrdts-new/PN_counter/App_new.fst interface/App_new.fsti",
	"fstar.exe mrdts-new/Grow-only_set/App_new.fst interface/App_new.fsti interface/Set_extended.fsti",
	"fstar.exe mrdts-new/Grow-only_map/App_new.fst interface/App_new.fsti interface/Set_extended.fsti interface/Map_extended.fsti",
	"fstar.exe mrdts-new/Observed-remove_set/App_new.fst interface/App_new.fsti interface/Set_extended.fsti interface/Map_extended.fsti",
	"fstar.exe mrdts-new/Map/App_new.fst interface/App_new.fsti interface/Set_extended.fsti",
	"fstar.exe mrdts-new/Enable_wins_flag/App_new.fst interface/App_new.fsti interface/Set_extended.fsti interface/Map_extended.fsti",
	"fstar.exe mrdts-new/Observed-remove_set_eff_new/App_new_new.fst interface/Set_extended.fsti interface/Map_extended.fsti",
]

# Execute commands and measure execution time
results = []
total_execution_time = 0
for command in commands:
    execution_time = execute_command(command)
    if execution_time is not None:
        total_execution_time += execution_time
        results.append([command, f"{execution_time:.4f} seconds"])

# Print individual command execution times in tabular format
if results:
    print(tabulate(results, headers=["Command", "Execution Time"]))
    print(f"\nOverall execution time: {total_execution_time:.4f} seconds")
else:
    print("No results to display.")
