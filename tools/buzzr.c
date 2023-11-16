/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

Buzzr is a fuzzer for selfie ...

*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void implement_buzzed_exit(uint64_t* context);

uint64_t buzz_read(uint64_t* buffer, uint64_t bytes_to_read);

void implement_buzzed_read(uint64_t* context);

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t buzzed_input = 0;

uint64_t number_of_buzzed_inputs = 0;

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_BUZZES = 256;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t handle_buzzed_system_call(uint64_t* context);

uint64_t handle_buzzed_page_fault(uint64_t* context);

uint64_t handle_buzzed_timer(uint64_t* context);

uint64_t handle_buzzed_exception(uint64_t* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t EXITCODE_OUTOFTIME = 100;

// -----------------------------------------------------------------
// ------------------------- BUZZING ENGINE ------------------------
// -----------------------------------------------------------------

uint64_t buzzr(uint64_t* to_context);

uint64_t selfie_buzz();

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void implement_buzzed_exit(uint64_t* context) {
  // parameter;
  uint64_t signed_int_exit_code;

  if (debug_syscalls) {
    printf("(exit): ");
    print_register_hexadecimal(REG_A0);
    printf(" |- ->\n");
  }

  signed_int_exit_code = *(get_regs(context) + REG_A0);

  set_exit_code(context, sign_shrink(signed_int_exit_code, SYSCALL_BITWIDTH));
}

uint64_t buzz_read(uint64_t* buffer, uint64_t bytes_to_read) {
  if (number_of_buzzed_inputs > 0) {
    if (number_of_buzzed_inputs < MAX_BUZZES)
      buzzed_input = (buzzed_input + 1) % MAX_BUZZES;
    else
      return sign_extend(-1, SYSCALL_BITWIDTH);
  }

  *buffer = buzzed_input;

  number_of_buzzed_inputs = number_of_buzzed_inputs + 1;

  return bytes_to_read;
}

void implement_buzzed_read(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  // local variables
  uint64_t read_total;
  uint64_t bytes_to_read;
  uint64_t failed;
  uint64_t* buffer;
  uint64_t actually_read;

  if (debug_syscalls) {
    printf("(read): ");
    print_register_value(REG_A0);
    printf(",");
    print_register_hexadecimal(REG_A1);
    printf(",");
    print_register_value(REG_A2);
    printf(" |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A0);
  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  if (debug_read)
    printf("%s: trying to read %lu bytes from file with descriptor %lu into buffer at virtual address 0x%08lX\n", selfie_name,
      size,
      fd,
      (uint64_t) vbuffer);

  read_total = 0;

  bytes_to_read = WORDSIZE;

  failed = 0;

  while (size > 0) {
    if (size < bytes_to_read)
      bytes_to_read = size;

    if (is_virtual_address_valid(vbuffer, WORDSIZE))
      if (is_data_stack_heap_address(context, vbuffer))
        if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
          buffer = translate_virtual_to_physical(get_pt(context), vbuffer);

          actually_read = buzz_read(buffer, bytes_to_read);

          if (actually_read == bytes_to_read) {
            read_total = read_total + actually_read;

            size = size - actually_read;

            if (size > 0)
              vbuffer = vbuffer + WORDSIZE;
          } else {
            if (signed_less_than(0, actually_read))
              read_total = read_total + actually_read;

            size = 0;
          }
        } else {
          failed = 1;

          size = 0;

          printf("%s: reading into virtual address 0x%08lX failed because the address is unmapped\n", selfie_name, (uint64_t) vbuffer);
        }
      else {
        failed = 1;

        size = 0;

        printf("%s: reading into virtual address 0x%08lX failed because the address is in an invalid segment\n", selfie_name, (uint64_t) vbuffer);
      }
    else {
      failed = 1;

      size = 0;

      printf("%s: reading into virtual address 0x%08lX failed because the address is invalid\n", selfie_name, (uint64_t) vbuffer);
    }
  }

  if (failed)
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    *(get_regs(context) + REG_A0) = read_total;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_read)
    printf("%s: actually read %lu bytes from file with descriptor %lu\n", selfie_name, read_total, fd);

  if (debug_syscalls) {
    printf(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t handle_buzzed_system_call(uint64_t* context) {
  uint64_t a7;

  set_exception(context, EXCEPTION_NOEXCEPTION);

  set_ec_syscall(context, get_ec_syscall(context) + 1);

  a7 = *(get_regs(context) + REG_A7);

  if (a7 == SYSCALL_BRK) {
    if (is_gc_enabled(context))
      implement_gc_brk(context);
    else
      implement_brk(context);
  } else if (a7 == SYSCALL_READ) {
    implement_buzzed_read(context);
  } else if (a7 == SYSCALL_WRITE)
    implement_write(context);
  else if (a7 == SYSCALL_OPENAT)
    implement_openat(context);
  else if (a7 == SYSCALL_EXIT) {
    implement_buzzed_exit(context);

    // TODO: exit only if all contexts have exited
    return EXIT;
  } else {
    printf("%s: unknown system call %lu\n", selfie_name, a7);

    set_exit_code(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

  return DONOTEXIT;
}

uint64_t handle_buzzed_page_fault(uint64_t* context) {
  uint64_t page;

  set_exception(context, EXCEPTION_NOEXCEPTION);

  set_ec_page_fault(context, get_ec_page_fault(context) + 1);

  page = get_fault(context);

  // TODO: reuse frames
  if (pavailable()) {
    map_page(context, page, (uint64_t) palloc());

    if (is_heap_address(context, virtual_address_of_page(page)))
      set_mc_mapped_heap(context, get_mc_mapped_heap(context) + PAGESIZE);

    return DONOTEXIT;
  } else {
    set_exit_code(context, sign_shrink(EXITCODE_OUTOFPHYSICALMEMORY, SYSCALL_BITWIDTH));

    return EXIT;
  }
}

uint64_t handle_buzzed_timer(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  set_ec_timer(context, get_ec_timer(context) + 1);

  set_exit_code(context, sign_shrink(EXITCODE_OUTOFTIME, SYSCALL_BITWIDTH));

  return EXIT;
}

uint64_t handle_buzzed_exception(uint64_t* context) {
  uint64_t exception;

  exception = get_exception(context);

  if (exception == EXCEPTION_SYSCALL)
    return handle_buzzed_system_call(context);
  else if (exception == EXCEPTION_PAGEFAULT)
    return handle_buzzed_page_fault(context);
  else if (exception == EXCEPTION_DIVISIONBYZERO)
    return handle_division_by_zero(context);
  else if (exception == EXCEPTION_TIMER)
    return handle_buzzed_timer(context);
  else {
    printf("%s: context %s threw uncaught exception: ", selfie_name, get_name(context));
    print_exception(exception, get_fault(context));
    println();

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }
}

// -----------------------------------------------------------------
// ------------------------- BUZZING ENGINE ------------------------
// -----------------------------------------------------------------

uint64_t buzzr(uint64_t* to_context) {
  uint64_t timeout;
  uint64_t* from_context;

  timeout = TIMESLICE;

  while (1) {
    from_context = mipster_switch(to_context, timeout);

    if (get_parent(from_context) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      to_context = get_parent(from_context);

      timeout = TIMEROFF;
    } else if (handle_buzzed_exception(from_context) == EXIT)
      return get_exit_code(from_context);
    else {
      // TODO: scheduler should go here
      to_context = from_context;

      timeout = TIMESLICE;
    }
  }
}

uint64_t selfie_buzz() {
  uint64_t keep_buzzing;
  uint64_t exit_code;

  if (string_compare(argument, "-")) {
    if (number_of_remaining_arguments() > 0) {
      if (code_size == 0) {
        printf("%s: nothing to buzz\n", selfie_name);

        return EXITCODE_BADARGUMENTS;
      }

      reset_interpreter();
      reset_profiler();
      reset_microkernel();

      init_memory(atoi(peek_argument(0)));

      run = 1;

      printf("%s: buzzing %s with %luMB physical memory\n", selfie_name,
        binary_name,
        PHYSICALMEMORYSIZE / MEGABYTE);
      printf("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);

      TIMESLICE = 10000000;

      keep_buzzing = 1;

      while (keep_buzzing) {
        current_context = create_context(MY_CONTEXT, 0);

        // assert: number_of_remaining_arguments() > 0

        boot_loader(current_context);

        // current_context is ready to run

        exit_code = buzzr(current_context);

        if (number_of_buzzed_inputs == 0) {
          printf("%s: unbuzzed %lu-bit RISC-U binary %s terminating with exit code %ld\n", selfie_name,
            WORDSIZEINBITS,
            binary_name,
            sign_extend(exit_code, SYSCALL_BITWIDTH));

          keep_buzzing = 0;
        } else if (number_of_buzzed_inputs < MAX_BUZZES) {
          if (exit_code != 0)
            if (exit_code != EXITCODE_OUTOFTIME)
              printf("%s: %lu-bit RISC-U binary %s buzzed with %ld terminating with exit code %ld\n", selfie_name,
                WORDSIZEINBITS,
                binary_name,
                buzzed_input,
                sign_extend(exit_code, SYSCALL_BITWIDTH));

          if (pavailable() == 0)
            keep_buzzing = 0;
        } else
          keep_buzzing = 0;
      }

      printf("%s: <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n", selfie_name);

      run = 0;

      printf("%s: ################################################################################\n", selfie_name);

      return EXITCODE_NOERROR;
    } else
      return EXITCODE_BADARGUMENTS;
  } else
    return EXITCODE_BADARGUMENTS;
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main(int argc, char** argv) {
  uint64_t exit_code;

  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();
  init_system();
  init_target();
  init_kernel();

  exit_code = selfie(1);

  if (exit_code == EXITCODE_MOREARGUMENTS)
    exit_code = selfie_buzz();

  return exit_selfie(exit_code, " - ...");
}