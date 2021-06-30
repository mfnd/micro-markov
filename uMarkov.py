#! /usr/bin/python
import sys
from markov_parser import Parser

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Please provide an input file")
        sys.exit(0)

    input_file = open(sys.argv[1])
    parser = Parser(input_file.read())
    model = parser.parse()
    model.check_all_specs()
