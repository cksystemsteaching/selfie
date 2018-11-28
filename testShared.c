// ./selfie -c testShared.c -cry 1  2
//                               /  \
//                         private  shared
//

uint64_t shared = 0;
uint64_t* shared_array = (uint64_t*) 0;

uint64_t main() {
    uint64_t id;

    shared_array = malloc(1048576);

    id = fork();

    if (id == 0) {

        *(shared_array + 4096) = 5;

    } else {
      wait();

    }

    //return shared;
    return *(shared_array + 4096);
}
