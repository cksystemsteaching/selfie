# python script to set Module arguments in an emscripten generated html file
import sys
import os.path

def get_html_code(html_file):
    with open(html_file, "r") as html:
        return html.readlines()

def get_index_and_line_num(string, html_source_list):
    assert(len(html_source_list) > 0)
    return [(i, line) for i, line in enumerate(html_source_list) if string in line]

def build_arg_string(args, line):
    # preserving the formatting
    whitespace = line.split("var")[0]
    argumentString = whitespace + "\targuments: ["
    for arg in args:
        argumentString = argumentString + make_string_literal(arg) + ","

    # remove trailing "," and close arg list
    argumentString = argumentString[:-1] + "],\n"

    return argumentString

def insert_args_into_html(html_lines, args, at_idx):
    # removing existing arguments list
    if "arguments: [" in html_lines[at_idx + 1]:
        html_lines.pop(at_idx + 1)

    # insert our created arguments into the html contents
    html_lines.insert(at_idx + 1, args)

def write_html(html_file, html_lines):
    with open(html_file, "w") as html:
        html.writelines(html_lines)

# set arguments to the arguments specified on the command line
def set_args(html_file, args):
    html_lines = get_html_code(html_file)

    module = get_index_and_line_num("var Module", html_lines)
    # We must find this declaration to proceed
    assert(len(module) == 1)

    index = module[0][0]
    line = module[0][1]

    if ("var Module") in line:
        arg_string = build_arg_string(args, line)

        print("Built arg string:\n\n" + arg_string)
        insert_args_into_html(html_lines, arg_string, index)

        write_html(html_file, html_lines)

        # arguments are set.
        return
    else:
        # var Module was not found in the specified html file
        print("Could not find a line containing definition of: var Module\n")
        print("An emcc generated html file must be present or the Module must be defined as in an emcc generated html file for this script to work.\n")
        sys.exit(1)

def make_string_literal(string):
    return "\"" + string + "\""

# returns a list of filenames specified on the command line
def extract_filenames(args):
    return [args[i+1] for i, arg in enumerate(args) if arg == '-o' or arg == '-s']

def generate_html_for_download(filename, preserved_whitespace):
    html = preserved_whitespace + "Module.FS.chmod('" + filename + "', 777);\n"
    html = html + preserved_whitespace + "var bytes = Module.FS.readFile('" + filename + "').buffer;\n"
    html = html + preserved_whitespace + "var blob = new Blob([bytes], {type: 'octet/stream'});\n"
    html = html + preserved_whitespace + "url = window.URL.createObjectURL(blob);\n"
    html = html + preserved_whitespace + "hiddenLink.href = url;\n"
    html = html + preserved_whitespace + "hiddenLink.download = '" + filename + "';\n"
    html = html + preserved_whitespace + "hiddenLink.click();\n"
    html = html + preserved_whitespace + "window.URL.revokeObjectURL(url);\n\n"
    return html

def build_postRun_string(args, line):
    # preserving the formatting
    whitespace = line.split("var")[0]
    argumentString = whitespace + "\targuments: ["
    for arg in args:
        argumentString = argumentString + make_string_literal(arg) + ","

    # remove trailing "," and close arg list
    argumentString = argumentString[:-1] + "],\n"

    return argumentString

def insert_postRun_into_html(html_lines, postRun, at_idx):
    # removing existing arguments list
    if "postRun: [" in html_lines[at_idx + 1]:
        html_lines.pop(at_idx + 1)

    # insert our created arguments into the html contents
    html_lines.insert(at_idx + 1, args)

def remove_existing_postRun(html_lines):
    postRun = get_index_and_line_num("postRun:", html_lines)
    postRun_index = postRun[0][0]

    # remove postRun definition
    while "print: " not in html_lines[postRun_index]:
        html_lines.pop(postRun_index)

def modify_postRun(html_lines, filenames):
    postRun = get_index_and_line_num("postRun:", html_lines)
    whitespace = postRun[0][1].split("postRun")[0]
    new_postRun = whitespace + "postRun: (function () {\n"

    whitespace_with_tab = whitespace + "\t"
    download_lines = ""
    for filename in filenames:
        download_lines = download_lines + generate_html_for_download(filename, whitespace_with_tab)

    new_postRun = new_postRun + download_lines + whitespace + "}),\n"

    remove_existing_postRun(html_lines)
    original_postRun_index = postRun[0][0]
    html_lines.insert(original_postRun_index, new_postRun)

def set_up_auto_downloads(html_file, filenames):
    print("Will now set up downloads\n")
    html_lines = get_html_code(html_file)
    module = get_index_and_line_num("var Module", html_lines)
    assert(len(module) == 1)

    module_declaration_index = module[0][0]

    # only add hidden link if it is not present yet
    if "spinnerElement" in html_lines[module_declaration_index - 2]:
        hidden_link_def = "\tvar hiddenLink = document.createElement('a');\n"
        hidden_link_def = hidden_link_def + "\tdocument.body.appendChild(hiddenLink);\n"
        hidden_link_def = hidden_link_def + "\thiddenLink.style = 'display: none';\n"

        # add hidden link
        html_lines.insert(module_declaration_index - 1, hidden_link_def)
    else:
        assert("hiddenLink.style" in html_lines[module_declaration_index - 2])

    modify_postRun(html_lines, filenames)
    print("Updated postRun.")

    write_html(html_file, html_lines)

def arg_parser(html_file, args):
    set_args(html_file, args)
    print("Arguments set.\n")

    if "-o" in args or "-s" in args:
        print("Setting up auto downloads of produced files")
        filenames = extract_filenames(args)
        print("Target file names:")
        print(filenames)
        set_up_auto_downloads(html_file, filenames)

if __name__ == "__main__":
    #move_file("here", "there")
    if len(sys.argv) < 3:
        print("Usage: python3 argument_setter.py <html> <arg1> ...")
        sys.exit(1)
    if os.path.isfile(sys.argv[1]):
        arg_parser(sys.argv[1], sys.argv[2:])
    else:
        print("Error:\nCould not find file: " + sys.argv[1] + "\nAn emcc generated html file must be present for this script to work.")
        sys.exit(1)