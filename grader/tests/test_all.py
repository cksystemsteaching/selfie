from unittest import TestSuite, TextTestRunner

from grader.tests.test_compilable import TestCompilable
from grader.tests.test_mipster_execution import TestMipsterExecution
from grader.tests.test_riscv_instruction import TestRiscvInstruction
from grader.tests.test_bulk_grader import TestBulkGrader
from grader.tests.test_execution_timeout import TestExecutionTimeout
from grader.tests.test_robustness import TestRobustness
from grader.tests.test_grading import TestGrading

def suite():
    suite = TestSuite()

    suite.addTest(TestCompilable())
    suite.addTest(TestMipsterExecution())
    suite.addTest(TestRiscvInstruction())
    suite.addTest(TestBulkGrader())
    suite.addTest(TestExecutionTimeout())
    suite.addTest(TestRobustness())
    suite.addTest(TestGrading())

    return suite

if __name__ == '__main__':
    runner = TextTestRunner()
    runner.run(suite())