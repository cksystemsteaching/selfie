from unittest import TestSuite, TextTestRunner

from grader.tests.test_compilable import TestCompilable
from grader.tests.test_mipster_execution import TestMipsterExecution
from grader.tests.test_riscv_instruction import TestRiscvInstruction
from grader.tests.test_bulk_grader import TestBulkGrader
from grader.tests.test_execution_timeout import TestExecutionTimeout

def suite():
    suite = TestSuite()
    suite.addTest(TestCompilable())
    suite.addTest(TestMipsterExecution())
    suite.addTest(TestRiscvInstruction())
    suite.addTest(TestBulkGrader())
    suite.addTest(TestExecutionTimeout())
    return suite

if __name__ == '__main__':
    runner = TextTestRunner()
    runner.run(suite())