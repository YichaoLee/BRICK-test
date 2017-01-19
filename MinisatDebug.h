#ifndef MINISATDEBUG_H
#define MINISATDEBUG_H

namespace Minisat {
	static inline uint32_t hash(uint32_t x);
	static inline uint32_t hash(uint64_t x);
	static inline uint32_t hash(int32_t x);
	static inline uint32_t hash(int64_t x);
}

#endif