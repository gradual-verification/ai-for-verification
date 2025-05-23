_Noreturn void external_func(void);
//@ requires true;
//@ ensures false;

_Noreturn static void static_proxy_func(void)
//@ requires true;
//@ ensures false;
{
	external_func();
}

_Noreturn inline void inline_proxy_func(void)
//@ requires true;
//@ ensures false;
{
	external_func();
}

_Noreturn static inline void static_inline_proxy_func(void)
//@ requires true;
//@ ensures false;
{
	external_func();
}
