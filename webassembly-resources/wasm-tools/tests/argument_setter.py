# python script to set Module arguments in an emscripten generated html file
import sys
import os.path

def get_html_code(html_file):
    with open(html_file, "r") as html:
        return html.readlines()

def return_line_and_index(string, html_source_list):
    print(len(html_source_list))
    return [(i, line) for i, line in enumerate(html_source_list) if string in line]

# set arguments to the arguments specified on the command line
def set_args(html_file, args):
    html_lines = get_html_code(html_file)
    for index, line in enumerate(html_lines):
        if ("var Module") in line:
            # preserving the formatting
            whitespace = line.split("var")[0]
            argumentString = whitespace + "\targuments: ["
            for arg in args:
                argumentString = argumentString + make_string_literal(arg) + ","

            # remove trailing "," and close list
            argumentString = argumentString[:-1] + "],\n"

            print("Setting arguments as:\n\n" + argumentString)

            # removing existing arguments line
            if "arguments: [" in contents[index+1]:
                contents.pop(index+1)

            # insert our created arguments into the html contents
            contents.insert(index + 1, argumentString)

            with open(html_file, "w") as resulting_html:
                resulting_html.writelines(contents)

            # arguments are set.
            return

        # var Module was not found in the specified html file
        print("Could not find a line containing: var Module = {\n")
        print("An emcc generated html file must be present or the Module must be defined as in an emcc generated html file for this script to work.\n")
        sys.exit(1)

    # error accessing html file
    print("Could not access file: " + html_file + "\n")
    sys.exit(1)

def make_string_literal(string):
    return "\"" + string + "\""

def arg_parser():
    #check if -o is in the arguments
    pass

    #move a file or directory (src) to another location (dst) and return the destination
def move_file(f, to):
    print("Moving: %s\nTo: %s\n", "from","to")
    #shutil.move()

if __name__ == "__main__":
    print(return_line_and_index("var Module", ["var Module"]))

#move_file("here", "there")
    if len(sys.argv) < 3:
        print("Usage: python3 argument_setter.py <html> <arg1> ...")
        sys.exit(1)
    if os.path.isfile(sys.argv[1]):
        set_args(sys.argv[1], sys.argv[2:])
    else:
        print("Error:\nCould not find file: " + sys.argv[1] + "\nAn emcc generated html file must be present for this script to work.")
        sys.exit(1)