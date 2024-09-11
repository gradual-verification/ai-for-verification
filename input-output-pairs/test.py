import os
import subprocess

def run_verifast_on_c_files():
    # Get the current working directory
    current_directory = os.getcwd()
    # Get a sorted list of subdirectories
    subdirs = sorted([d for d in os.listdir(current_directory) \
                if os.path.isdir(os.path.join(current_directory, d))])
    
    # Define the output file path
    output_file = os.path.join(current_directory, "verifast_errors.txt")

    if os.path.exists(output_file):
        try:
            os.remove(output_file)
        except Exception as e:
            print(f"Error: {e}")

    i = 1
    # Iterate over each subdirectory in the current directory
    for subdir in subdirs:
        subdir_path = os.path.join(current_directory, subdir)
        
        # Check if the path is a directory
        if os.path.isdir(subdir_path):
            # Look for C files in the subdirectory
            for file in os.listdir(subdir_path):
                # Check if the file ends with ".c" and does NOT end with "_m.c", "_n.c", or "_w.c"
                if file.endswith(".c") and not (file.endswith("_m.c") or file.endswith("_n.c") or file.endswith("_w.c")):
                    c_file_path = os.path.join(subdir_path, file)
                    
                    # Run VeriFast on the C file
                    try:
                        print(f"{i}: Running VeriFast on {c_file_path}...")
                        result = subprocess.run(["verifast", c_file_path], capture_output=True, text=True)
                        
                        # Print the output of VeriFast
                        print(result.stdout)
                        if result.stderr:
                            print(f"Error: {result.stderr}")
                        
                        if "0 errors found" not in result.stdout or "Program linked successfully" not in result.stdout:
                            with open(output_file, 'a') as f:
                                f.write(f"\n{i}: Running VeriFast on {c_file_path}...")
                                f.write(result.stdout)
                                if result.stderr:
                                    f.write("\nErrors:\n")
                                    f.write(result.stderr)
                        
                        i += 1
                    
                    except FileNotFoundError:
                        print("Error: VeriFast executable not found. Please ensure VeriFast is installed and added to your PATH.")
                    except Exception as e:
                        print(f"An error occurred while running VeriFast: {e}")

if __name__ == "__main__":
    run_verifast_on_c_files()
