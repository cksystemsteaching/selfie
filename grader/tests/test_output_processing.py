from unittest import TestCase, main

from lib.output_processing import (contains_name, filter_status_messages, has_no_compile_warnings, has_no_bootstrapping_compile_warnings,
                                   is_interleaved_output, is_permutation_of)

class TestOutputProcessing(TestCase):

    def test_name_detection(self):
        self.assertTrue(contains_name(
            './selfie: This is Christian Moesl\'s Selfie!\n./selfie: bla')[0])
        self.assertFalse(contains_name(
            './selfie: This is adjlsjasldkjaslkds Selfie!\n./selfie: bla')[0])

    def test_status_message_filter(self):
        output = './selfie: this is an important message\n' \
            + 'normal program output\n' \
            + 'c:\\\\basdlkasjdl\\selfie.exe: this is another important message\n' \
            + 'second output\n'

        filtered = filter_status_messages(output)

        self.assertEqual(filtered, "normal program outputsecond output")

    def test_interleaved_output(self):
        self.assertTrue(is_interleaved_output(
            'aaabbbcccddd', 'abcd', 3))
        self.assertTrue(is_interleaved_output(
            'aabcbacdbcdd', 'abcd', 3))
        self.assertFalse(is_interleaved_output(
            'abcdabcdabcd', 'abcd', 3)[0])

    def test_permutation_detection(self):
        self.assertTrue(is_permutation_of('1 2 3', [1, 2, 3])[0])
        self.assertTrue(is_permutation_of('3 1 2', [1, 2, 3])[0])
        self.assertTrue(is_permutation_of('1 6 7', [6, 1, 7])[0])
        self.assertFalse(is_permutation_of('1', [1, 2])[0])
        self.assertFalse(is_permutation_of('1 2 3', [1, 2])[0])
        self.assertFalse(is_permutation_of('1 2 4', [1, 2, 3])[0])
        self.assertTrue(is_permutation_of('1 2 3\n', [1, 2, 3])[0], 'should ignore newlines')


    def test_selfie_warning_detection(self):
        output = """
./selfie: this is the selfie system from selfie.cs.uni-salzburg.at with
./selfie: 64-bit unsigned integers and 64-bit pointers hosted on macOS
./selfie: selfie compiling selfie.c with starc
./selfie: warning in selfie.c in line 291: type mismatch, uint64_t* expected but uint64_t found
./selfie: 321982 characters read in 11194 lines and 1518 comments
./selfie: with 194060(60.27%) characters in 46746 actual symbols
"""
        return_code = 0

        succeeded, _warning = has_no_compile_warnings(return_code, output)

        self.assertFalse(succeeded)


    def test_clang_warning_detection(self):
        output = """
cc -Wall -Wextra -pedantic -O3 -m64 -D'uint64_t=unsigned long' selfie.c -o selfie
selfie.c:11191:2: warning: no newline at end of file [-Wnewline-eof]
}
 ^
1 warning generated.
"""
        return_code = 0

        succeeded, _warning = has_no_bootstrapping_compile_warnings(return_code, output)

        self.assertFalse(succeeded)


    def test_gcc_warning_detection(self):
        output = """
selfie.c: In function 'init_library':
selfie.c:294:22: warning: assignment to 'long unsigned int' from 'long unsigned int *' makes integer from pointer without a cast [-Wint-conversion]
  294 |   SIZEOFUINT64       = ((uint64_t*) SELFIE_URL + 1) - (uint64_t) SELFIE_URL;
      |
"""
        return_code = 0

        succeeded, _warning = has_no_bootstrapping_compile_warnings(return_code, output)

        self.assertFalse(succeeded)


if __name__ == '__main__':
    main()
