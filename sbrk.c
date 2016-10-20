#include <unistd.h>
#include <stdlib.h>
int *a = 0; 
int *now = 0; 
void *sbrk(int p) {
	int *ret = 0;
	if (a == 0) {
		a = (int*)malloc(32 * 1024 * 1024 * sizeof(char)); 
		now = a; 
	} 

	if (p == 0) 
		return now; 
	else {
		ret = now; 
		now = now + p/4; 
		return (void*)ret; 
	}
	return now; 
}
