import os
import subprocess


def run_test_cases(testcases_dir, expected_output_file):
    expected_output = {}

    # Read the expected output file
    with open(expected_output_file, 'r') as f:
        lines = f.readlines()
        for i in range(0, len(lines), 2):
            filename = lines[i].strip()
            result = lines[i + 1].strip()
            expected_output[filename] = result

    # Walk through all subdirectories in the testcases folder
    for root, dirs, files in os.walk(testcases_dir):
        for file in files:
            if file.endswith('.cnf'):
                file_path = os.path.join(root, file)
                print(f'Running: {file}')

                # Run the command and capture output
                result = subprocess.run(['python3', 'satisfiability.py', file_path], capture_output=True, text=True)
                output = result.stdout.strip()  # or use `result.stderr` if your output is printed there

                print("\texpected : output")
                print("\t     " + expected_output[file] + " : " + output + "\n")
                if output != expected_output[file]:
                    print(f'\t{file}: Output does NOT match expected result.\n')


if __name__ == '__main__':
    testcases_directory = 'testcases'
    expected_output_file = 'testcases/answers.out'
    run_test_cases(testcases_directory, expected_output_file)
