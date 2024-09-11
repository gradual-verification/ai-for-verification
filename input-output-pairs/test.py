import os
import subprocess

def run_verifast_on_c_files():
    # Get the current working directory
    current_directory = os.getcwd()
    
    # Define the output file path
    output_file = os.path.join(current_directory, "verifast_errors.txt")

    if os.path.exists(output_file):
        try:
            os.remove(output_file)
        except Exception as e:
            print(f"Error: {e}")

    i = 1
    # Iterate over each subdirectory in the current directory
    for dirpath, dirnames, filenames in os.walk(current_directory):
        for filename in filenames:
            # Check if the file ends with ".c" and does NOT end with "_m.c", "_n.c", or "_w.c"
            if filename.endswith(".c") and not (filename.endswith("_m.c") or \
                    filename.endswith("_n.c") or filename.endswith("_w.c")):

                c_file_path = os.path.join(dirpath, filename)
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
