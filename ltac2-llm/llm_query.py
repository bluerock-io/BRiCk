#
# Copyright (C) 2024-2025 BlueRock Security, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#
import sys
import openai
import os
from openai import OpenAI

def main():

    delimiter = "\nEOF\n"
    input_data = sys.stdin.read()

    if delimiter in input_data:
        input_text = input_data.split(delimiter)[0]
    else:
        input_text = input_data

    try:
        with open("/builds/openaikey", "r") as f:
            api_key = f.readline().strip()

        client = OpenAI(api_key=api_key)
        chat_completion = client.chat.completions.create(
            messages=[
                {
                    "role": "system",
                    "content": "You are an expert in logic, formal methods, constructive type theory, dependent type theory, Coq (Gallina, Ltac, Ltac2)",
                },
                {
                    "role": "user",
                    "content": input_text,
                }
            ],
            model="gpt-4o",
        )
        output = chat_completion.choices[0].message.content
    except Exception as e:
        output = f"Error: {str(e)}"

    print(output)  # Print to stdout

if __name__ == "__main__":
    main()
