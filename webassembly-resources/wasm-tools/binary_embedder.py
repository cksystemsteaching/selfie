# This script embeds an existing wasm binary into a minimal html file
# by reading the binary bytes and transforming them into a list of hexadecimal # numbers. This list is then embedded into the html and a WebAssemblyInstance is
# created
# The created html file can then be extended by exporting relevant functions
# defined in the binary and using them with JavaScript.
#
# As an example, consider this .wat file:
#
# (module
#   (func $MULTIPLY (param i32) (param i32) (result i32)
#     get_local 0
#     get_local 1
#     i32.mul
#     return
#   )
#
#   (export "MUL" (func $MULTIPLY))
# )
#
# After translating this .wat into its corresponding .wasm format (using
# wat2wasm from the Webassembly binary toolkit (https://github.com/WebAssembly/wabt)),
# embedding the resulting .wasm using this script into a file called math.html,
# the function MULTIPLY can be called with JS by creating a function:
#
# var mul = WebAssemblyInstance.exports.MUL;
#
# and calling it to multiply two 32-bit integers:
# mul(2, 2)

import sys

def formatted_byte_list(bin_file):
    hex_list = []
    with open(bin_file,'rb') as f:
        byte = f.read(1)
        while byte:
            hex_list.append("0x" + byte.hex())
            # Do stuff with byte.
            byte = f.read(1)

    return hex_list

def create_html(html_file_name, hex_list):
    html_code = "<!DOCTYPE html>\n<html>\n<head><meta charset=\"UTF-8\"> </head>\n<body>\n\t"
    html_code += "<script>\n\t\tvar binary = new Uint8Array("
    html_code += str(hex_list)
    html_code += ");\n\n\t\tvar WebAssemblyInstance = new WebAssembly.Instance(new WebAssembly.Module(binary));\n\n\t</script>\n</body>\n</html>"
    with open(html_file_name, "w") as html:
        html.write(html_code)

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: \npython3 embedder.py <target-file-name> <wasm-binary-file-name>\n")
        sys.exit(1)

    print("Will create/modify: " + sys.argv[1])
    print("With binary: " + sys.argv[2])
    create_html(sys.argv[1], formatted_byte_list(sys.argv[2]))