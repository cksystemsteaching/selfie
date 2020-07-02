#!/usr/bin/python3

import sys, getopt

import csv

from collections import namedtuple

def main(argv):
    inputfile = ''
    outputfile = ''
    try:
        opts, args = getopt.getopt(argv,"hi:o:",["ifile=","ofile="])
    except getopt.GetoptError:
        print ('examr.py -i <inputfile> -o <outputfile>')
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-h':
            print ('examr.py -i <inputfile> -o <outputfile>')
            sys.exit()
        elif opt in ("-i", "--ifile"):
            inputfile = arg
        elif opt in ("-o", "--ofile"):
            outputfile = arg
    if inputfile != '':
        with open(inputfile, mode='r') as csv_file:
            csv_reader = csv.DictReader(csv_file)
            if outputfile != '':
                with open(outputfile, mode='w') as csv_file:
                    students = dict()

                    qa_count       = 0
                    q_length_count = 0
                    a_length_count = 0
                    for row in csv_reader:
                        qa_count       += 1
                        q_length_count += len(row['Ask Question'])
                        a_length_count += len(row['Answer Question'])

                        entry = namedtuple('Entry', ['number_of_qas', 'q_total', 'q_length', 'a_total', 'a_length'])

                        if row['Email address'] not in students:
                            students[row['Email address']] = entry(
                                    number_of_qas = 1,
                                    q_total       = float(row['Grade Question']),
                                    q_length      = len(row['Ask Question']),
                                    a_total       = float(row['Grade Answer']),
                                    a_length      = len(row['Answer Question'])
                                )
                        else:
                            students[row['Email address']] = entry(
                                    number_of_qas = students[row['Email address']].number_of_qas + 1,
                                    q_total       = students[row['Email address']].q_total + float(row['Grade Question']),
                                    q_length      = students[row['Email address']].q_length + len(row['Ask Question']),
                                    a_total       = students[row['Email address']].a_total + float(row['Grade Answer']),
                                    a_length      = students[row['Email address']].a_length + len(row['Answer Question']),
                                )
                    print(f'Total number of Q&As {qa_count}')

                    fieldnames = 'Google Apps Email', 'PLUS Email', 'Total Average', 'Number of Q&As', 'Length of Answers', 'Length of Questions', 'Totel Length of Q&As', 'Question Average', 'Answer Average'
                    csv_writer = csv.DictWriter(csv_file, fieldnames=fieldnames)

                    csv_writer.writeheader()
                    student_count = 0
                    for student in list(students):
                        student_count += 1
                        csv_writer.writerow({
                                'Google Apps Email': student,
                                'Total Average': (students[student].q_total + students[student].a_total) / students[student].number_of_qas,
                                'Number of Q&As': students[student].number_of_qas,
                                'Length of Answers': students[student].a_length,
                                'Length of Questions': students[student].q_length,
                                'Totel Length of Q&As': students[student].q_length + students[student].a_length,
                                'Question Average': students[student].q_total / students[student].number_of_qas,
                                'Answer Average': students[student].a_total / students[student].number_of_qas
                            })

                    print(f'Number of students: {student_count}')
                    print(f'Average number of Q&As per student: {qa_count / student_count}')
                    print(f'Average length of answers per student: {a_length_count / student_count}')
                    print(f'Average length of questions per student: {q_length_count / student_count}')
                    print(f'Average length of Q&As per student: {(q_length_count + a_length_count) / student_count}')

if __name__ == "__main__":
    main(sys.argv[1:])