#include "glean/rts/error.h"

#include <sstream>
#include <vector>

#define UNW_LOCAL_ONLY
#include <libunwind.h>
#include <folly/Demangle.h>

namespace facebook {
namespace glean {
namespace rts {

[[noreturn]] void raiseError(const std::string& msg) {
  // NOTE: we can't use folly::symbolizer here, see T40546255
  std::ostringstream out;
  out << msg;

  std::vector<char> buffer(256);
  unw_context_t context;
  unw_cursor_t cursor;
  if (unw_getcontext(&context) == 0
        && unw_init_local(&cursor, &context) == 0) {
    size_t n = 0;

    out << "\nStack trace:\n";

    do {
      unw_word_t dummy;
      if (unw_get_proc_name(&cursor, buffer.data(), buffer.size(), &dummy)
          != 0) {
        break;
      }
      out << "  " << folly::demangle(buffer.data()) << '\n';
      ++n;
    } while (n < 10 && unw_step(&cursor) > 0);
    if (n == 10) {
      out << "  ...";
    }
  } else {
    out << "\nStack trace unavailable";
  }

  throw std::runtime_error(out.str());
}

}
}
}
