/***
 * Declaration: external_func
 *
 * Description:
 * A placeholder for an external function that is known to never return.
 * The implementation is not provided in this file.
 */
_Noreturn void external_func(void);

/***
 * Function: static_proxy_func
 *
 * Description:
 * A static proxy function that simply calls the non-returning external function.
 * Being `static`, it is visible only within this translation unit.
 */
_Noreturn static void static_proxy_func(void)
{
	external_func();
}

/***
 * Function: inline_proxy_func
 *
 * Description:
 * An inline proxy function that calls the non-returning external function.
 * Declared `inline` to suggest inlining at the call site.
 */
_Noreturn inline void inline_proxy_func(void)
{
	external_func();
}

/***
 * Function: static_inline_proxy_func
 *
 * Description:
 * A function that is both `static` and `inline`, combining local visibility
 * with inlining suggestion, and known to never return.
 */
_Noreturn static inline void static_inline_proxy_func(void)
{
	external_func();
}
