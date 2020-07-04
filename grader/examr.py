#!/usr/bin/env python3

import sys, getopt

import csv

# requires installing textdistance: pip3 install "textdistance[extras]"
import textdistance

class Student:
    def __init__(self, q_total, q_length, a_total, a_length):
        self.number_of_qas = 1
        self.q_total       = q_total
        self.q_length      = q_length
        self.q_similarity  = 0
        self.a_total       = a_total
        self.a_length      = a_length
        self.a_similarity  = 0

def process_qas(csv_file):
    csv_reader = csv.DictReader(csv_file)

    students = dict()

    emails = []

    questions = []
    answers   = []

    q_total_length = 0
    a_total_length = 0

    for row in csv_reader:
        emails.append(row['Email address'])

        questions.append(row['Ask Question'])
        q_total_length += len(row['Ask Question'])
        answers.append(row['Answer Question'])
        a_total_length += len(row['Answer Question'])

        if row['Email address'] not in students:
            students[row['Email address']] = Student(
                float(row['Grade Question']),
                len(row['Ask Question']),
                float(row['Grade Answer']),
                len(row['Answer Question']))
        else:
            students[row['Email address']].number_of_qas += 1
            students[row['Email address']].q_total       += float(row['Grade Question'])
            students[row['Email address']].q_length      += len(row['Ask Question'])
            students[row['Email address']].a_total       += float(row['Grade Answer'])
            students[row['Email address']].a_length      += len(row['Answer Question'])

    return students, emails, questions, answers, q_total_length, a_total_length

def generate_csv(students, csv_file):
    fieldnames = 'Google Apps Email', 'PLUS Email', 'Total Average', 'Number of Q&As', 'Length of Answers', 'Similarity of Answers', 'Length of Questions', 'Similarity of Questions', 'Totel Length of Q&As', 'Question Average', 'Answer Average'

    csv_writer = csv.DictWriter(csv_file, fieldnames=fieldnames)

    csv_writer.writeheader()

    for student in students.items():
        csv_writer.writerow({
            'Google Apps Email': student[0],
            'Total Average': (student[1].q_total + student[1].a_total) / student[1].number_of_qas / 2,
            'Number of Q&As': student[1].number_of_qas,
            'Length of Answers': student[1].a_length,
            'Similarity of Answers': student[1].a_similarity,
            'Length of Questions': student[1].q_length,
            'Similarity of Questions': student[1].q_similarity,
            'Totel Length of Q&As': student[1].q_length + student[1].a_length,
            'Question Average': student[1].q_total / student[1].number_of_qas,
            'Answer Average': student[1].a_total / student[1].number_of_qas
        })

def compute_similarity(text_blocks):
    similarity = [ [0] * len(text_blocks) for i in range(len(text_blocks)) ]

    for x in range(len(text_blocks)):
        for y in range(len(text_blocks)):
            if x != y:
                similarity[x][y] = textdistance.cosine.normalized_similarity(text_blocks[x], text_blocks[y])
                if (x < y and similarity[x][y] > 0.98):
                    print(f'>>> Similarity {similarity[x][y]} at [{x},{y}]:\n{text_blocks[x]}\n===\n{text_blocks[y]}\n<<<\n')

    return similarity

def assign_similarity(students, emails, q_similarity, a_similarity):
    for x in range(len(emails)):
        student = students[emails[x]]

        for y in range(len(emails)):
            if x != y:
                student.q_similarity += q_similarity[x][y]
                student.a_similarity += a_similarity[x][y]

        if (len(emails) > 1):
            # normalize again
            student.q_similarity /= len(emails) - 1
            student.a_similarity /= len(emails) - 1

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
        with open(inputfile, mode='r') as csv_input_file:
            if outputfile != '':
                with open(outputfile, mode='w') as csv_output_file:
                    students, emails, questions, answers, q_total_length, a_total_length = process_qas(csv_input_file)

                    q_similarity = compute_similarity(questions)
                    a_similarity = compute_similarity(answers)

                    assign_similarity(students, emails, q_similarity, a_similarity)

                    generate_csv(students, csv_output_file)

                    print(f'Number of students: {len(students)}')
                    print(f'Total number of Q&As {len(questions)}')
                    print(f'Average number of Q&As per student: {len(questions) / len(students)}')
                    print(f'Average length of answers per student: {a_total_length / len(students)}')
                    print(f'Average length of questions per student: {q_total_length / len(students)}')
                    print(f'Average length of Q&As per student: {(q_total_length + a_total_length) / len(students)}')

if __name__ == "__main__":
    main(sys.argv[1:])