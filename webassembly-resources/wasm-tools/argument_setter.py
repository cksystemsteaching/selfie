# python script to set Module arguments in an emscripten generated html file
import sys
import os.path

# set arguments to the arguments specified on the command line
def set_args(html_file, args):
    with open(html_file, "r") as html:
        contents = html.readlines()
        for index, line in enumerate(contents):
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

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python3 argument_setter.py <html> <arg1> ...")
        sys.exit(1)
    if os.path.isfile(sys.argv[1]):
        set_args(sys.argv[1], sys.argv[2:])
    else:
        print("Error:\nCould not find file: " + sys.argv[1] + "\nAn emcc generated html file must be present for this script to work.")
        sys.exit(1)