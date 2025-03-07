import os
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import reset_env
from lazy_solver import offline_lazy_smt_solver


def test_all_cases(test_cases_folder):
    # Get and sort all .smt2 files in the folder
    test_files = sorted([f for f in os.listdir(test_cases_folder) if f.endswith(".smt2")])

    for f in test_files:
        file_path = os.path.join(test_cases_folder, f)
        # Reset the PySMT environment for each file.
        reset_env()
        parser = SmtLibParser()
        with open(file_path) as file:
            try:
                script = parser.get_script(file)
                formula = script.get_last_formula()
            except Exception as e:
                print(f"{f}: Error while parsing: {e}")
                continue

        try:
            result = offline_lazy_smt_solver(formula)
            res_str = "SATISFIABLE" if result else "UNSATISFIABLE"
            print(f"{f}: {res_str}")
        except Exception as e:
            print(f"{f}: Error during solving: {e}")


if __name__ == '__main__':
    test_cases_folder = "test_cases"
    test_all_cases(test_cases_folder)
