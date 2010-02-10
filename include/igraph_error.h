/* -*- mode: C -*-  */
/* 
   IGraph library.
   Copyright (C) 2003, 2004, 2005  Gabor Csardi <csardi@rmki.kfki.hu>
   MTA RMKI, Konkoly-Thege Miklos st. 29-33, Budapest 1121, Hungary
   
   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc.,  51 Franklin Street, Fifth Floor, Boston, MA 
   02110-1301 USA

*/

#ifndef IGRAPH_ERROR_H
#define IGRAPH_ERROR_H

#undef __BEGIN_DECLS
#undef __END_DECLS
#ifdef __cplusplus
# define __BEGIN_DECLS extern "C" {
# define __END_DECLS }
#else
# define __BEGIN_DECLS /* empty */
# define __END_DECLS /* empty */
#endif

__BEGIN_DECLS

/* This file contains the igraph error handling.
 * Most bits are taken literally from the GSL library (with the GSL_
 * prefix renamed to IGRAPH_), as I couldn't find a better way to do
 * them. */

/**
 * \section errorhandlingbasics Error handling basics
 * 
 * <para>\a igraph functions can run into various problems preventing them 
 * from normal operation: the user might have supplied invalid arguments,
 * eg. a non-square matrix when a square-matrix was expected, or the program 
 * has run out of memory while some more memory allocation is required, etc.
 * </para>
 * 
 * <para>By default \a igraph aborts the program when it runs into an 
 * error. While this behavior might be good enough for smaller programs, 
 * it is without doubt avoidable in larger projects. Please read further
 * if your project requires more sophisticated error handling. You can 
 * safely skip the rest of this chapter otherwise.
 * </para>
 */

/**
 * \section errorhandlers Error handlers
 *
 * <para>
 * If \a igraph runs into an error - an invalid argument was supplied
 * to a function, or we've ran out of memory - the control is
 * transferred to the \emb error handler \eme function.
 * </para><para>
 * The default error handler is \ref igraph_error_handler_abort which
 * prints an error message and aborts the program.
 * </para>
 * <para>
 * The \ref igraph_set_error_handler() function can be used to set a new
 * error handler function of type \ref igraph_error_handler_t, see the
 * documentation of this type for details.
 * </para>
 * <para>
 * There are two other predefined error handler functions,
 * \ref igraph_error_handler_ignore and \ref igraph_error_handler_printignore, 
 * these deallocate the temporarily allocated memory (more about this
 * later) and return with the error code. The latter also prints an
 * error message. If you use these error handlers you need to take
 * care about possible errors yourself by checking the return value of
 * (almost) every non-void \a igraph function.
 * </para><para>
 * Independently of the error handler installed, all functions in the
 * library do their best to leave their arguments
 * \em semantically unchanged if an error
 * happens. By semantically we mean that the implementation of an
 * object supplied as an argument might change, but its
 * \quote meaning \endquote in most cases does not. The rare occasions
 * when this rule is violated are documented in this manual.
 * </para>
 */

/**
 * \section errorcodes Error codes
 * 
 * <para>Every \a igraph function which can fail return a
 * single integer error code. Some functions are very simple and
 * cannot run into any error, these may return other types, or
 * \type void as well. The error codes are defined by the
 * \ref igraph_error_type_t enumeration.
 * </para>
 */

/**
 * \section writing_error_handlers Writing error handlers
 *
 * <para>
 * The contents of the rest of this chapter might be useful only
 * for those who want to create an interface to \a igraph from another
 * language. Most readers can safely skip to the next chapter.
 * </para>
 * 
 * <para>
 * You can write and install error handlers simply by defining a
 * function of type \ref igraph_error_handler_t and calling
 * \ref igraph_set_error_handler(). This feature is useful for interface
 * writers, as \a igraph will have the chance to
 * signal errors the appropriate way, eg. the R interface defines an
 * error handler which calls the <function>error()</function>
 * function, as required by R, while the Python interface has an error
 * handler which raises an exception according to the Python way.
 * </para>
 * <para> 
 * If you want to write an error handler, your error handler should
 * call \ref IGRAPH_FINALLY_FREE() to deallocate all temporary memory to
 * prevent memory leaks.
 * </para>
 */

/**
 * \section error_handling_internals Error handling internals
 *
 * <para>
 * If an error happens, the functions in the library call the
 * \ref IGRAPH_ERROR macro with a textual description of the error and an
 * \a igraph error code. This macro calls (through the \ref
 * igraph_error() function) the installed error handler. Another useful
 * macro is \ref IGRAPH_CHECK(), this checks the return value of its
 * argument which is normally a function call, and calls \ref
 * IGRAPH_ERROR if it is not \c IGRAPH_SUCCESS. 
 * </para>
 */

/** 
 * \section deallocating_memory Deallocating memory
 *
 * <para>
 * If a function runs into an error (and the program is not aborted)
 * the error handler should deallocate all temporary memory. This is
 * done by storing the address and the destroy function of all temporary
 * objects in a stack. The \ref IGRAPH_FINALLY function declares an object as
 * temporary by placing its address in the stack. If an \a igraph function returns
 * with success it calls \ref IGRAPH_FINALLY_CLEAN() with the
 * number of objects to remove from the stack. If an error happens
 * however, the error handler should call \ref IGRAPH_FINALLY_FREE() to
 * deallocate each object added to the stack. This means that the
 * temporary objects allocated in the calling function (and etc.) will
 * be freed as well.
 * </para>
 */

/**
 * \section writing_functions_error_handling Writing \a igraph functions with
 * proper error handling
 *
 * <para>
 * There are some simple rules to keep in order to have functions
 * behaving well in erroneous situations. First, check the arguments
 * of the functions and call \ref IGRAPH_ERROR if they are invalid. Second,
 * call \ref IGRAPH_FINALLY on each dynamically allocated object and call
 * \ref IGRAPH_FINALLY_CLEAN() with the proper argument before returning. Third, use
 * IGRAPH_CHECK on all \a igraph function calls which can generate errors.
 * </para>
 * <para>
 * The size of the stack used for this bookkeeping is fixed, and
 * small. If you want to allocate several objects, write a destroy
 * function which can deallocate all of these. See the
 * <filename>adjlist.c</filename> file in the
 * \a igraph source for an example.
 * </para>
 * <para> 
 * For some functions these mechanisms are simply not flexible
 * enough. These functions should define their own error handlers and
 * restore the error handler before they return.
 * </para>
 */

/**
 * \section error_handling_threads Error handling and threads
 *
 * <para>
 * It is likely that the \a igraph error handling
 * method is \em not thread-safe, mainly because of
 * the static global stack which is used to store the address of the
 * temporarily allocated objects. This issue might be addressed in a
 * later version of \a igraph.
 * </para>
 */

/**
 * \typedef igraph_error_handler_t
 * \brief Type of error handler functions.
 * 
 * This is the type of the error handler functions.
 * \param reason Textual description of the error.
 * \param file The source file in which the error is noticed.
 * \param line The number of the line in the source file which triggered
 *   the error
 * \param igraph_errno The \a igraph error code.
 */

typedef void igraph_error_handler_t (const char * reason, const char * file,
				     int line, int igraph_errno);

/**
 * \var igraph_error_handler_abort
 * \brief Abort program in case of error.
 *
 * The default error handler, prints an error message and aborts the
 * program. 
 */

extern igraph_error_handler_t igraph_error_handler_abort;

/**
 * \var igraph_error_handler_ignore
 * \brief Ignore errors.
 *
 * This error handler frees the temporarily allocated memory and returns
 * with the error code. 
 */

extern igraph_error_handler_t igraph_error_handler_ignore;

/**
 * \var igraph_error_handler_printignore
 * \brief Print and ignore errors.
 * 
 * Frees temporarily allocated memory, prints an error message to the
 * standard error and returns with the error code. 
 */

extern igraph_error_handler_t igraph_error_handler_printignore;

/**
 * \function igraph_set_error_handler
 * \brief Set a new error handler.
 *
 * Installs a new error handler. If called with 0, it installs the
 * default error handler (which is currently
 * \ref igraph_error_handler_abort). 
 * \param new_handler The error handler function to install.
 * \return The old error handler function. This should be saved and
 *   restored if \p new_handler is not needed any
 *   more.
 */

igraph_error_handler_t*
igraph_set_error_handler(igraph_error_handler_t* new_handler);

/**
 * \typedef igraph_error_type_t
 * \brief Error code type.
 * These are the possible valued returned by \a igraph functions.
 * Note that these are interesting only if you defined an error handler
 * with \ref igraph_set_error_handler(). Otherwise the program is aborted 
 * and the function causing the error never returns.
 * 
 * \enumval IGRAPH_SUCCESS The function successfully completed its task.
 * \enumval IGRAPH_FAILURE Something went wrong. You'll almost never
 *    meet this error as normally more specific error codes are used.
 * \enumval IGRAPH_ENOMEM There wasn't enough memory to allocate
 *    on the heap. 
 * \enumval IGRAPH_PARSEERROR A parse error was found in a file.
 * \enumval IGRAPH_EINVAL A parameter's value is invalid. Eg. negative
 *    number was specified as the number of vertices.
 * \enumval IGRAPH_EXISTS A graph/vertex/edge attribute is already
 *    installed with the given name.
 * \enumval IGRAPH_EINVEVECTOR Invalid vector of vertex ids. A vertex id
 *    is either negative or bigger than the number of vertices minus one.
 * \enumval IGRAPH_EINVVID Invalid vertex id, negative or too big.
 * \enumval IGRAPH_NONSQUARE A non-square matrix was received while a
 *    square matrix was expected.
 * \enumval IGRAPH_EINVMODE Invalid mode parameter.
 * \enumval IGRAPH_EFILE A file operation failed. Eg. a file doesn't exist,
 *   or the user ha no rights to open it.
 * \enumval IGRAPH_UNIMPLEMENTED Attempted to call an unimplemented or
 *   disabled (at compile-time) function.
 * \enumval IGRAPH_DIVERGED A numeric algorithm failed to converge.
 * \enumval IGRAPH_ARPACK_PROD Matrix-vector product failed.
 * \enumval IGRAPH_ARPACK_NPOS N must be positive.
 * \enumval IGRAPH_ARPACK_NEVNPOS NEV must be positive.
 * \enumval IGRAPH_ARPACK_NCVSMALL NCV must be bigger.
 * \enumval IGRAPH_ARPACK_NONPOSI Maximum number of iterations should be positive.
 * \enumval IGRAPH_ARPACK_WHICHINV Invalid WHICH parameter.
 * \enumval IGRAPH_ARPACK_BMATINV Invalid BMAT parameter.
 * \enumval IGRAPH_ARPACK_WORKLSMALL WORKL is too small.
 * \enumval IGRAPH_ARPACK_TRIDERR LAPACK error in tridiagonal eigenvalue calculation.
 * \enumval IGRAPH_ARPACK_ZEROSTART Starting vector is zero.
 * \enumval IGRAPH_ARPACK_MODEINV MODE is invalid.
 * \enumval IGRAPH_ARPACK_MODEBMAT MODE and BMAT are not compatible.
 * \enumval IGRAPH_ARPACK_ISHIFT ISHIFT must be 0 or 1.
 * \enumval IGRAPH_ARPACK_NEVBE NEV and WHICH='BE' are incompatible.
 * \enumval IGRAPH_ARPACK_NOFACT Could not build an Arnoldi factorization.
 * \enumval IGRAPH_ARPACK_FAILED No eigenvalues to sufficient accuracy.
 * \enumval IGRAPH_ARPACK_HOWMNY HOWMNY is invalid.
 * \enumval IGRAPH_ARPACK_HOWMNYS HOWMNY='S' is not implemented.
 * \enumval IGRAPH_ARPACK_EVDIFF Different number of converged Ritz values.
 * \enumval IGRAPH_ARPACK_SHUR Error from calculation of a real Schur form.
 * \enumval IGRAPH_ARPACK_LAPACK LAPACK (dtrevc) error for calculating eigenvectors.
 * \enumval IGRAPH_ARPACK_UNKNOWN Unkown ARPACK error.
 * \enumval IGRAPH_ENEGLOOP Negative loop detected while calculating shortest paths.
 * \enumval IGRAPH_EINTERNAL Internal error, likely a bug in igraph.
 * \enumval IGRAPH_EDIVZERO Big integer division by zero.
 */

typedef enum {
  IGRAPH_SUCCESS       = 0,
  IGRAPH_FAILURE       = 1,
  IGRAPH_ENOMEM        = 2,
  IGRAPH_PARSEERROR    = 3,
  IGRAPH_EINVAL        = 4,
  IGRAPH_EXISTS        = 5,
  IGRAPH_EINVEVECTOR   = 6,
  IGRAPH_EINVVID       = 7,
  IGRAPH_NONSQUARE     = 8,
  IGRAPH_EINVMODE      = 9,
  IGRAPH_EFILE         = 10,
  IGRAPH_UNIMPLEMENTED = 12,
  IGRAPH_INTERRUPTED   = 13,
  IGRAPH_DIVERGED      = 14,
  IGRAPH_ARPACK_PROD      = 15,
  IGRAPH_ARPACK_NPOS      = 16,
  IGRAPH_ARPACK_NEVNPOS   = 17,
  IGRAPH_ARPACK_NCVSMALL  = 18,
  IGRAPH_ARPACK_NONPOSI   = 19,
  IGRAPH_ARPACK_WHICHINV  = 20,
  IGRAPH_ARPACK_BMATINV   = 21,
  IGRAPH_ARPACK_WORKLSMALL= 22,
  IGRAPH_ARPACK_TRIDERR   = 23,
  IGRAPH_ARPACK_ZEROSTART = 24,
  IGRAPH_ARPACK_MODEINV   = 25,
  IGRAPH_ARPACK_MODEBMAT  = 26,
  IGRAPH_ARPACK_ISHIFT    = 27,
  IGRAPH_ARPACK_NEVBE     = 28,
  IGRAPH_ARPACK_NOFACT    = 29,
  IGRAPH_ARPACK_FAILED    = 30,
  IGRAPH_ARPACK_HOWMNY    = 31,
  IGRAPH_ARPACK_HOWMNYS   = 32,
  IGRAPH_ARPACK_EVDIFF    = 33,
  IGRAPH_ARPACK_SHUR      = 34,
  IGRAPH_ARPACK_LAPACK    = 35,
  IGRAPH_ARPACK_UNKNOWN   = 36,
  IGRAPH_ENEGLOOP         = 37,
  IGRAPH_EINTERNAL        = 38,
  IGRAPH_ARPACK_MAXIT     = 39,
  IGRAPH_ARPACK_NOSHIFT   = 40,
  IGRAPH_ARPACK_REORDER   = 41,
  IGRAPH_EDIVZERO         = 42
} igraph_error_type_t;

/**
 * \define IGRAPH_ERROR
 * \brief Trigger an error.
 * 
 * \a igraph functions usually use this macro when they notice an error.
 * It calls
 * \ref igraph_error() with the proper parameters and if that returns 
 * the macro returns the "calling" function as well, with the error
 * code. If for some (suspicious) reason you want to call the error
 * handler without returning from the current function, call
 * \ref igraph_error() directly.
 * \param reason Textual description of the error. This should be
 *   something more explaning than the text associated with the error
 *   code. Eg. if the error code is \c IGRAPH_EINVAL,
 *   its asssociated text (see  \ref igraph_strerror()) is "Invalid
 *   value" and this string should explain which parameter was invalid
 *   and maybe why. 
 * \param igraph_errno The \a igraph error code.
 */

#define IGRAPH_ERROR(reason,igraph_errno) \
       do { \
       igraph_error (reason, __FILE__, __LINE__, igraph_errno) ; \
       return igraph_errno ; \
       } while (0)

/**
 * \function igraph_error
 * \brief Trigger an error.
 *
 * \a igraph functions usually call this fuction (most often via the 
 * \ref IGRAPH_ERROR macro) if they notice an error.
 * It calls the currently installed error handler function with the
 * supplied arguments. 
 *
 * \param reason Textual description of the error.
 * \param file The source file in which the error was noticed.
 * \param line The number of line in the source file which triggered the
 *   error.
 * \param igraph_errno The \a igraph error code.
 * \return the error code (if it returns)
 */

int igraph_error(const char *reason, const char *file, int line,
		 int igraph_errno);

/**
 * \function igraph_strerror
 * \brief Textual description of an error.
 * 
 * This is a simple utility function, it gives a short general textual
 * description for an \a igraph error code.
 * 
 * \param igraph_errno The \a igraph error code.
 * \return pointer to the textual description of the error code.
 */

const char* igraph_strerror(const int igraph_errno);

#define IGRAPH_ERROR_SELECT_2(a,b)       ((a) != IGRAPH_SUCCESS ? (a) : ((b) != IGRAPH_SUCCESS ? (b) : IGRAPH_SUCCESS))
#define IGRAPH_ERROR_SELECT_3(a,b,c)     ((a) != IGRAPH_SUCCESS ? (a) : IGRAPH_ERROR_SELECT_2(b,c))
#define IGRAPH_ERROR_SELECT_4(a,b,c,d)   ((a) != IGRAPH_SUCCESS ? (a) : IGRAPH_ERROR_SELECT_3(b,c,d))
#define IGRAPH_ERROR_SELECT_5(a,b,c,d,e) ((a) != IGRAPH_SUCCESS ? (a) : IGRAPH_ERROR_SELECT_4(b,c,d,e))

/* Now comes the more conveninent error handling macro arsenal.
 * Ideas taken from exception.{h,c} by Laurent Deniau see
 * http://cern.ch/Laurent.Deniau/html/oopc/oopc.html#Exceptions for more 
 * information. We don't use the exception handling code though.  */

struct igraph_i_protectedPtr {
  int all;
  void *ptr;
  void (*func)(void*);
};

typedef void igraph_finally_func_t (void*);

void IGRAPH_FINALLY_REAL(void (*func)(void*), void* ptr);

/**
 * \function IGRAPH_FINALLY_CLEAN
 * \brief Signal clean deallocation of objects.
 * 
 * Removes the specified number of objects from the stack of
 * temporarily allocated objects. Most often this is called just
 * before returning from a function.
 * \param num The number of objects to remove from the bookkeeping
 *   stack. 
 */

void IGRAPH_FINALLY_CLEAN(int num); 

/**
 * \function IGRAPH_FINALLY_FREE
 * \brief Deallocate all registered objects.
 *
 * Calls the destroy function for all objects in the stack of
 * temporarily allocated objects. This is usually called only from an
 * error handler. It is \em not appropriate to use it
 * instead of destroying each unneeded object of a function, as it
 * destroys the temporary objects of the caller function (and so on)
 * as well.
 */

void IGRAPH_FINALLY_FREE(void);

/**
 * \function IGRAPH_FINALLY_STACK_SIZE
 * \brief Returns the number of registered objects.
 *
 * Returns the number of objects in the stack of temporarily allocated
 * objects. This function is handy if you write an own igraph routine and
 * you want to make sure it handles errors properly. A properly written
 * igraph routine should not leave pointers to temporarily allocated objects
 * in the finally stack, because otherwise an \ref IGRAPH_FINALLY_FREE call
 * in another igraph function would result in freeing these objects as well
 * (and this is really hard to debug, since the error will be not in that
 * function that shows erroneous behaviour). Therefore, it is advised to
 * write your own test cases and examine \ref IGRAPH_FINALLY_STACK_SIZE
 * before and after your test cases - the numbers should be equal.
 */
int IGRAPH_FINALLY_STACK_SIZE(void);

/**
 * \define IGRAPH_FINALLY_STACK_EMPTY
 * \brief Returns true if there are no registered objects, false otherwise.
 *
 * This is just a shorthand notation for checking that
 * \ref IGRAPH_FINALLY_STACK_SIZE is zero.
 */
#define IGRAPH_FINALLY_STACK_EMPTY (IGRAPH_FINALLY_STACK_SIZE() == 0)

/**
 * \define IGRAPH_FINALLY
 * \brief Register an object for deallocation.
 * \param func The address of the function which is normally called to
 *   destroy the object.
 * \param ptr Pointer to the object itself.
 * 
 * This macro places the address of an object, together with the
 * address of its destructor in a stack. This stack is used if an
 * error happens to deallocate temporarily allocated objects to
 * prevent memory leaks.
 */

#define IGRAPH_FINALLY(func,ptr) \
  IGRAPH_FINALLY_REAL((igraph_finally_func_t*)(func), (ptr))

/**
 * \define IGRAPH_CHECK
 * \brief Check the return value of a function call.
 *
 * \param a An expression, usually a function call.
 * 
 * Executes the expression and checks its value. If this is not
 * \c IGRAPH_SUCCESS, it calls \ref IGRAPH_ERROR with
 * the value as the error code. Here is an example usage:
 * \verbatim IGRAPH_CHECK(vector_push_back(&amp;v, 100)); \endverbatim
 * 
 * </para><para>There is only one reason to use this macro when writing 
 * \a igraph functions. If the user installs an error handler which
 * returns to the auxilary calling code (like \ref
 * igraph_error_handler_ignore and \ref
 * igraph_error_handler_printignore), and the \a igraph function
 * signalling the error is called from another \a igraph function 
 * then we need to make sure that the error is propagated back to 
 * the auxilary (ie. non-igraph) calling function. This is achieved
 * by using <function>IGRAPH_CHECK</function> on every \a igraph
 * call which can return an error code.
 */

#if (defined(__GNUC__) && GCC_VERSION_MAJOR >= 3)
#  define IGRAPH_UNLIKELY(a) __builtin_expect((a), 0)
#  define IGRAPH_LIKELY(a)   __builtin_expect((a), 1)
#else
#  define IGRAPH_UNLIKELY(a) a
#  define IGRAPH_LIKELY(a)   a
#endif

#define IGRAPH_CHECK(a) do { \
                 int igraph_i_ret=(a); \
                 if (IGRAPH_UNLIKELY(igraph_i_ret != 0)) {\
                     IGRAPH_ERROR("", igraph_i_ret); \
                 } } while (0)


typedef igraph_error_handler_t igraph_warning_handler_t;

igraph_warning_handler_t*
igraph_set_warning_handler(igraph_warning_handler_t* new_handler);

extern igraph_warning_handler_t igraph_warning_handler_print;

int igraph_warning(const char *reason, const char *file, int line,
		   int igraph_errno);

#define IGRAPH_WARNING(reason) \
       do { \
         igraph_warning(reason, __FILE__, __LINE__, -1); \
       } while (0)

__END_DECLS

#endif
