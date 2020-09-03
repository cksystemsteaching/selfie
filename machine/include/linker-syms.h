#ifndef KERN_LINKER_SYMS
#define KERN_LINKER_SYMS

extern const void* _payload_start;
extern const void* _payload_end;

extern const void* _text_start;
extern const void* _text_end;

extern const void* _rodata_start;
extern const void* _rodata_end;

extern const void* _data_start;
extern const void* _data_end;

extern const void* _bss_start;
extern const void* _bss_end;

extern const void* __SDATA_BEGIN__;


#endif /* KERN_LINKER_SYMS */
