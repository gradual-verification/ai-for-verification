import subprocess
import time

def run_llama2(prompt):
    try:
        # Start the llama3 model using subprocess
        print("Starting the llama3 model...")
        process = subprocess.Popen(
            ['ollama', 'run', 'llama3'],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            shell=True
        )
        
        # Allow some time for the model to start
        print("Waiting for the model to initialize...")
        time.sleep(10)
        
        # Send the prompt to the model
        print(f"Sending prompt: {prompt}")
        stdout, stderr = process.communicate(input=prompt + '\n', timeout=30)
        
        # Print the output
        print("Output:", stdout)
        if stderr:
            print("Errors:", stderr)
        
        return stdout.strip()
    
    except subprocess.TimeoutExpired:
        process.kill()
        stdout, stderr = process.communicate()
        print("Process timed out.")
        print("Output:", stdout)
        print("Errors:", stderr)
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == '__main__':
    user_prompt = 'Why is the sky blue?'
    response = run_llama2(user_prompt)
    print("Model Response:", response)
