#!/usr/bin/env python3

# requires: pip3 install "textdistance[extras]"

import textdistance

def get_cosine_similarity(string1, string2):
    return textdistance.cosine.normalized_similarity(string1, string2)

import re

# requires: pip3 install langid laserembeddings
# and also: python3 -m laserembeddings download-models

from langid import classify
from laserembeddings import Laser

def get_vectors(strings):
    languages = []

    for string in strings:
        languages.append(classify(string)[0])

    corpus = [string.lower() for string in strings]
    corpus = [" ".join(string.splitlines()) for string in corpus]
    corpus = [re.sub(r'\W+', ' ', string) for string in corpus]

    return Laser().embed_sentences(corpus, lang=languages)

# requires: pip3 install sklearn

from sklearn.metrics.pairwise import cosine_similarity

def get_lasered_cosine_similarity(vector1, vector2):
    return cosine_similarity([vector1], [vector2])[0][0]

def formality(text):
    # list more restrictive patterns first
    formal = "(uint64_t\*?)|(_?[a-z]+(_[a-z]+)+)|('.')|(\d)|(\+)|(\-)|(\*)|(\/)|(%)|(\|)|(==)|(!=)|(<=)|(<)|(>=)|(>)|(=)|(lui)|(addi)|(ld)|(sd)|(add)|(sub)|(mul)|(divu)|(remu)|(sltu)|(beq)|(jalr)|(jal)|(ecall)"
    return len(re.findall(formal, text, re.IGNORECASE))

class Student:
    def __init__(self, firstname, lastname, q_total, q_length, q_formality, a_total, a_length, a_formality):
        self.number_of_qas = 1
        self.firstname     = firstname
        self.lastname      = lastname
        self.q_total       = q_total
        self.q_length      = q_length
        self.q_formality   = q_formality
        self.q_similarity  = float(0)
        self.a_total       = a_total
        self.a_length      = a_length
        self.a_formality   = a_formality
        self.a_similarity  = float(0)

def compute_similarity(students, emails, row_num, message, strings, old_strings, old_emails, old_row_num, old_firstnames, old_lastnames):
    all_strings = strings + old_strings

    vectors = get_vectors(all_strings)

    similarity = [ [float(0)] * len(all_strings) for i in range(len(strings)) ]

    for x in range(len(strings)):
        for y in range(len(all_strings)):
            if x < y:
                # similarity[x][y] = get_cosine_similarity(strings[x], all_strings[y])
                similarity[x][y] = get_lasered_cosine_similarity(vectors[x], vectors[y])

                if similarity[x][y] > 0.95:
                    print(f'{message} similarity {similarity[x][y]} at:')
                    print(f'[{row_num[x]}]: {emails[x]} ({students[emails[x]].firstname} {students[emails[x]].lastname})')
                    if y <= len(strings):
                        print(f'[{row_num[y]}]: {emails[y]} ({students[emails[y]].firstname} {students[emails[y]].lastname})')
                    else:
                        print(f'[{old_row_num[y - len(strings)]}]: {old_emails[y - len(strings)]} ({old_firstnames[y - len(strings)]} {old_lastnames[y - len(strings)]}) [old response]')
                    print(f'<<<\n{strings[x]}\n---\n{all_strings[y]}\n>>>\n')
            elif x > y:
                similarity[x][y] = similarity[y][x]
            else:
                similarity[x][y] = 1.0

    return similarity

def assign_similarity(students, emails, old_emails, q_similarity, a_similarity):
    all_emails = emails + old_emails

    for x in range(len(emails)):
        student = students[emails[x]]

        for y in range(len(all_emails)):
            if x != y:
                student.q_similarity += q_similarity[x][y]
                student.a_similarity += a_similarity[x][y]

        if (len(all_emails) > 1):
            # normalize again
            student.q_similarity /= len(all_emails) - 1
            student.a_similarity /= len(all_emails) - 1

import csv

def process_files(response_file, analysis_file, class_id, year, attempt):
    old_emails     = []
    old_row_num    = []
    old_firstnames = []
    old_lastnames  = []
    old_questions  = []
    old_answers    = []

    students = dict()

    emails      = []
    row_num     = []
    questions   = []
    answers     = []
    q_length    = 0
    q_formality = 0
    a_length    = 0
    a_formality = 0

    csv_reader = csv.DictReader(response_file)

    for i, row in enumerate(csv_reader, start=2):
        if (row['Class'] == class_id and row['Year'] == year and row['Attempt'] == attempt):
            emails.append(row['Username'])
            row_num.append(i)

            questions.append(row['Ask Question'])
            q_length    += len(row['Ask Question'])
            q_formality += formality(row['Ask Question'])

            answers.append(row['Answer Question'])
            a_length    += len(row['Answer Question'])
            a_formality += formality(row['Answer Question'])

            if row['Username'] not in students:
                students[row['Username']] = Student(
                    row['Firstname'],
                    row['Lastname'],
                    float(row['Grade Question']),
                    len(row['Ask Question']),
                    formality(row['Ask Question']),
                    float(row['Grade Answer']),
                    len(row['Answer Question']),
                    formality(row['Answer Question']))
            else:
                students[row['Username']].number_of_qas += 1
                students[row['Username']].q_total       += float(row['Grade Question'])
                students[row['Username']].q_length      += len(row['Ask Question'])
                students[row['Username']].q_formality   += formality(row['Ask Question'])
                students[row['Username']].a_total       += float(row['Grade Answer'])
                students[row['Username']].a_length      += len(row['Answer Question'])
                students[row['Username']].a_formality   += formality(row['Answer Question'])
        else:
            old_emails.append(row['Username'])
            old_row_num.append(i)
            old_firstnames.append(row['Firstname'])
            old_lastnames.append(row['Lastname'])
            old_questions.append(row['Ask Question'])
            old_answers.append(row['Answer Question'])

    q_similarity = compute_similarity(students, emails, row_num, "Question", questions, old_questions, old_emails, old_row_num, old_firstnames, old_lastnames)
    a_similarity = compute_similarity(students, emails, row_num, "Answer", answers, old_answers, old_emails, old_row_num, old_firstnames, old_lastnames)

    assign_similarity(students, emails, old_emails, q_similarity, a_similarity)

    fieldnames = 'Google Apps Email', 'Firstname', 'Lastname', 'Total Average', 'Number of Q&As', 'Length of Answers', 'Formality of Answers', 'Similarity of Answers', 'Length of Questions', 'Formality of Questions', 'Similarity of Questions', 'Totel Length of Q&As', 'Question Average', 'Answer Average'

    csv_writer = csv.DictWriter(analysis_file, fieldnames=fieldnames)

    csv_writer.writeheader()

    for student in students.items():
        csv_writer.writerow({
            'Google Apps Email': student[0],
            'Firstname': student[1].firstname,
            'Lastname': student[1].lastname,
            'Total Average': (student[1].q_total + student[1].a_total) / student[1].number_of_qas / 2,
            'Number of Q&As': student[1].number_of_qas,
            'Length of Answers': student[1].a_length,
            'Formality of Answers': student[1].a_formality,
            'Similarity of Answers': student[1].a_similarity,
            'Length of Questions': student[1].q_length,
            'Formality of Questions': student[1].q_formality,
            'Similarity of Questions': student[1].q_similarity,
            'Totel Length of Q&As': student[1].q_length + student[1].a_length,
            'Question Average': student[1].q_total / student[1].number_of_qas,
            'Answer Average': student[1].a_total / student[1].number_of_qas
        })

    print(f'Number of students: {len(students)}')
    print(f'Total number of Q&As {len(questions)}')
    print(f'Average number of Q&As per student: {len(questions) / len(students)}')
    print(f'Average length of answers per student: {a_length / len(students)}')
    print(f'Average formality of answers per student: {a_formality / len(students)}')
    print(f'Average length of questions per student: {q_length / len(students)}')
    print(f'Average formality of questions per student: {q_formality / len(students)}')
    print(f'Average length of Q&As per student: {(q_length + a_length) / len(students)}')

import sys, getopt

def main(argv):
    response_file = ''
    analysis_file = ''

    class_id = 'IOS'
    year     = '2019'
    attempt  = '2nd'

    try:
        opts, args = getopt.getopt(argv,'hr:a:c:y:t:',[])
    except getopt.GetoptError:
        print ('examr.py -r <responsefile> -a <analysisfile> -c class -y year -t attempt')
        sys.exit(2)

    for opt, arg in opts:
        if opt == '-h':
            print ('examr.py -r <responsefile> -a <analysisfile> -c class -y year -t attempt')
            sys.exit()
        elif opt == '-r':
            response_file = arg
        elif opt == '-a':
            analysis_file = arg
        elif opt == '-c':
            class_id = arg
        elif opt == '-y':
            year = arg
        elif opt == '-t':
            attempt = arg

    if response_file != '':
        with open(response_file, mode='r') as csv_response_file:
            if analysis_file != '':
                with open(analysis_file, mode='w') as csv_analysis_file:
                    process_files(csv_response_file, csv_analysis_file, class_id, year, attempt)

if __name__ == "__main__":
    main(sys.argv[1:])