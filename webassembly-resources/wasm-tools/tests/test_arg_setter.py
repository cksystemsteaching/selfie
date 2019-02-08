import argument_setter as arg_setter

def empty_file_test():
    with open("empty-file.html", "r") as test_html:
        content = test_html.readlines()
        assert(len([x for x in content if 'var Module' in x]) == 0)

def sanity_check1():
    with open("test-file-containing-var-Module.html", "r") as test_html:
        content = test_html.readlines()
        assert(len([x for x in content if 'var Module' in x]) == 1)


def san_check():
    with open("test-file-containing-var-Module.html", "r") as test_html:
        content = test_html.readlines()
        print([x for x in content if 'var Module' in x])

def call_arg_setter():
    pass

def test_stringify():
    string_literal = "\"hello world\""
    assert(arg_setter.make_string_literal("hello world") == string_literal)
    assert("\"x\"" in arg_setter.make_string_literal("x"))
    assert(len(arg_setter.make_string_literal("x"))== 3)

def test_html_parsing(html_file):
    with open(html_file, "r") as html:
        source = html.readlines()
        print(arg_setter.return_line_and_index("var Module" , source))
        assert(len(arg_setter.return_line_and_index("var Module" , source)) == 1)


if __name__ == "__main__":
    # san_check()
    sanity_check1()
    empty_file_test()
    test_stringify()
    test_html_parsing("test-file-containing-var-Module.html")