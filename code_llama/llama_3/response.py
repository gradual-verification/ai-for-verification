import requests
import json

def generate_response(prompt):
    url = "http://localhost:11434/api/generate"
    payload = {
        "model": "llama3",
        "prompt": prompt,
        "stream": False
    }
    headers = {
        'Content-Type': 'application/json'
    }

    try:
        response = requests.post(url, data=json.dumps(payload), headers=headers)
        
        # Check if the request was successful
        if response.status_code == 200:
            response_data = response.json()
            print("Model Response:", response_data)
            return response_data
        else:
            print(f"Request failed with status code: {response.status_code}")
            print("Response:", response.text)
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == '__main__':
    user_prompt = 'Why is the sky blue?'
    response = generate_response(user_prompt)
