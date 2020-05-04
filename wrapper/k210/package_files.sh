#!/usr/bin/bash

SBI_FILES_HEADER=sbi_files.h

pushd ../..
make
./selfie -c selfie.c -o selfie.m
popd

pushd ..

cat <<EOF >${SBI_FILES_HEADER}
#ifndef SBI_FILES
#define SBI_FILES


EOF

xxd -i ../selfie.c >>${SBI_FILES_HEADER}
printf "\n\n" >>${SBI_FILES_HEADER}
xxd -i ../selfie.m >>${SBI_FILES_HEADER}
cat <<EOF >>${SBI_FILES_HEADER}

#endif /* SBI_FILES */
EOF

sed -i -re 's/unsigned int _*(\w+) = ([0-9]+);/\#define \1 \2/g' ${SBI_FILES_HEADER}
sed -i -re 's/unsigned char _*/static const char /g' ${SBI_FILES_HEADER}

popd
