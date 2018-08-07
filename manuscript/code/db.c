void init_library();
void print(uint64_t* s);
void println();
void printf1(uint64_t* s, uint64_t* a1);

void db_init(uint64_t* name);

void     db_put(uint64_t* key, uint64_t values);
uint64_t db_get(uint64_t* key);
uint64_t db_exists(uint64_t* key);

uint64_t main(uint64_t argc, uint64_t* argv) {
  init_library();

  db_init("selfie.db");

  if (db_exists("key")) {
    printf1("exists: %d\n", db_get("key"));
    
    db_put("key", db_get("key") + 1);
  } else 
    db_put("key", 1);

  printf1("updated to: %d\n", db_get("key"));
} 