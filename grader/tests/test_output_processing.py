from unittest import TestCase, main

from lib.output_processing import (contains_name, filter_status_messages,
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
        self.assertTrue(is_permutation_of('123', [1, 2, 3]))
        self.assertTrue(is_permutation_of('312', [1, 2, 3]))
        self.assertTrue(is_permutation_of('167', [6, 1, 7]))
        self.assertFalse(is_permutation_of('1', [1, 2])[0])
        self.assertFalse(is_permutation_of('123', [1, 2])[0])
        self.assertFalse(is_permutation_of('124', [1, 2, 3])[0])



if __name__ == '__main__':
    main()
