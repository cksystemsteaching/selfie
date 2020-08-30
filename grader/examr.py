#!/usr/bin/env python3

import sys, getopt

import csv

import re

# requires: pip3 install "textdistance[extras]"

import textdistance

def get_cosine_similarity(string1, string2):
    return textdistance.cosine.normalized_similarity(string1, string2)

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
    def __init__(self, q_total, q_length, q_formality, a_total, a_length, a_formality):
        self.number_of_qas = 1
        self.q_total       = q_total
        self.q_length      = q_length
        self.q_formality   = q_formality
        self.q_similarity  = float(0)
        self.a_total       = a_total
        self.a_length      = a_length
        self.a_formality   = a_formality
        self.a_similarity  = float(0)

def read_old_qas(responsefiles):
    emails    = []
    questions = []
    answers   = []

    for responsefile in responsefiles:
        with open(responsefile, mode='r') as csv_file:
            csv_reader = csv.DictReader(csv_file)

            for row in csv_reader:
                emails.append(row['Email address'])
                questions.append(row['Ask Question'])
                answers.append(row['Answer Question'])

    return emails, questions, answers

def read_qas(csv_file):
    csv_reader = csv.DictReader(csv_file)

    students = dict()

    emails = []

    questions = []
    answers   = []

    q_length    = 0
    q_formality = 0

    a_length    = 0
    a_formality = 0

    for row in csv_reader:
        emails.append(row['Email address'])

        questions.append(row['Ask Question'])
        q_length    += len(row['Ask Question'])
        q_formality += formality(row['Ask Question'])

        answers.append(row['Answer Question'])
        a_length    += len(row['Answer Question'])
        a_formality += formality(row['Answer Question'])

        if row['Email address'] not in students:
            students[row['Email address']] = Student(
                float(row['Grade Question']),
                len(row['Ask Question']),
                formality(row['Ask Question']),
                float(row['Grade Answer']),
                len(row['Answer Question']),
                formality(row['Answer Question']))
        else:
            students[row['Email address']].number_of_qas += 1
            students[row['Email address']].q_total       += float(row['Grade Question'])
            students[row['Email address']].q_length      += len(row['Ask Question'])
            students[row['Email address']].q_formality   += formality(row['Ask Question'])
            students[row['Email address']].a_total       += float(row['Grade Answer'])
            students[row['Email address']].a_length      += len(row['Answer Question'])
            students[row['Email address']].a_formality   += formality(row['Answer Question'])

    return students, emails, questions, answers, q_length, q_formality, a_length, a_formality

def write_results(students, csv_file):
    fieldnames = 'Google Apps Email', 'PLUS Email', 'Total Average', 'Number of Q&As', 'Length of Answers', 'Formality of Answers', 'Similarity of Answers', 'Length of Questions', 'Formality of Questions', 'Similarity of Questions', 'Totel Length of Q&As', 'Question Average', 'Answer Average'

    csv_writer = csv.DictWriter(csv_file, fieldnames=fieldnames)

    csv_writer.writeheader()

    for student in students.items():
        csv_writer.writerow({
            'Google Apps Email': student[0],
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

def compute_similarity(message, strings, emails, old_strings, old_emails):
    all_strings = strings + old_strings
    all_emails  = emails + old_emails

    vectors = get_vectors(all_strings)

    similarity = [ [float(0)] * len(all_strings) for i in range(len(strings)) ]

    for x in range(len(strings)):
        for y in range(len(all_strings)):
            if x < y:
                # similarity[x][y] = get_cosine_similarity(strings[x], all_strings[y])
                similarity[x][y] = get_lasered_cosine_similarity(vectors[x], vectors[y])

                if similarity[x][y] > 0.95:
                    print(f'{message} similarity {similarity[x][y]} at [{x},{y}]:\n{emails[x]}\n{all_emails[y]}{" (old)" if y>len(strings) else ""}\n<<<\n{strings[x]}\n---\n{all_strings[y]}\n>>>\n')
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

def main(argv):
    oldresponsefiles = []
    responsefile     = ''
    analysisfile     = ''

    try:
        opts, args = getopt.getopt(argv,"ho:r:a:",["ofile=","rfile=","afile="])
    except getopt.GetoptError:
        print ('examr.py { -o <oldresponsesfile> } -r <responsefile> -a <analysisfile>')
        sys.exit(2)

    for opt, arg in opts:
        if opt == '-h':
            print ('examr.py { -o <oldresponsesfile> } -r <responsefile> -a <analysisfile>')
            sys.exit()
        elif opt in ("-o", "--ofile"):
            oldresponsefiles.append(arg)
        elif opt in ("-r", "--rfile"):
            responsefile = arg
        elif opt in ("-a", "--afile"):
            analysisfile = arg

    if responsefile != '':
        with open(responsefile, mode='r') as csv_responses_file:
            if analysisfile != '':
                with open(analysisfile, mode='w') as csv_analysis_file:
                    old_emails, old_questions, old_answers = read_old_qas(oldresponsefiles)

                    students, emails, questions, answers, q_length, q_formality, a_length, a_formality = read_qas(csv_responses_file)

                    q_similarity = compute_similarity("Question", questions, emails, old_questions, old_emails)
                    a_similarity = compute_similarity("Answer", answers, emails, old_answers, old_emails)

                    assign_similarity(students, emails, old_emails, q_similarity, a_similarity)

                    write_results(students, csv_analysis_file)

                    print(f'Number of students: {len(students)}')
                    print(f'Total number of Q&As {len(questions)}')
                    print(f'Average number of Q&As per student: {len(questions) / len(students)}')
                    print(f'Average length of answers per student: {a_length / len(students)}')
                    print(f'Average formality of answers per student: {a_formality / len(students)}')
                    print(f'Average length of questions per student: {q_length / len(students)}')
                    print(f'Average formality of questions per student: {q_formality / len(students)}')
                    print(f'Average length of Q&As per student: {(q_length + a_length) / len(students)}')

if __name__ == "__main__":
    main(sys.argv[1:])