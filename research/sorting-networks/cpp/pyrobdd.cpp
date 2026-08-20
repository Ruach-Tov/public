// pyrobdd.cpp — Python C extension wrapping the C++ ROBDD.
// Exposes the same interface as order_only.py's ROBDD class,
// so it can be used as a drop-in backend via dependency injection.
//
// Build: python3 setup.py build_ext --inplace
// Or:    g++ -shared -fPIC -O2 -std=c++17 $(python3-config --includes) \
//            -o pyrobdd$(python3-config --extension-suffix) pyrobdd.cpp
//
// Usage:
//   from pyrobdd import ROBDD, verify_sorts
//   bdd = ROBDD(16)
//   x0 = bdd.var(0)
//   ...
//
// Ruach Tov Collective, 2026. CC BY 4.0.

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include "robdd.hpp"

using namespace ruachtov;

// ============================================================
// ROBDD Python object
// ============================================================

typedef struct {
    PyObject_HEAD
    ROBDD* bdd;
    int nvars;
} PyROBDD;

static void PyROBDD_dealloc(PyROBDD* self) {
    delete self->bdd;
    Py_TYPE(self)->tp_free((PyObject*)self);
}

static int PyROBDD_init(PyROBDD* self, PyObject* args, PyObject* /*kwds*/) {
    int nvars;
    if (!PyArg_ParseTuple(args, "i", &nvars))
        return -1;
    if (nvars < 0) {
        PyErr_SetString(PyExc_ValueError, "nvars must be non-negative");
        return -1;
    }
    self->nvars = nvars;
    self->bdd = new ROBDD(nvars);
    return 0;
}

static PyObject* PyROBDD_var(PyROBDD* self, PyObject* args) {
    int i;
    if (!PyArg_ParseTuple(args, "i", &i)) return nullptr;
    if (i < 0 || i >= self->nvars) {
        PyErr_SetString(PyExc_IndexError, "variable index out of range");
        return nullptr;
    }
    return PyLong_FromLong(self->bdd->var(i));
}

static PyObject* PyROBDD_AND(PyROBDD* self, PyObject* args) {
    int a, b;
    if (!PyArg_ParseTuple(args, "ii", &a, &b)) return nullptr;
    return PyLong_FromLong(self->bdd->AND(a, b));
}

static PyObject* PyROBDD_OR(PyROBDD* self, PyObject* args) {
    int a, b;
    if (!PyArg_ParseTuple(args, "ii", &a, &b)) return nullptr;
    return PyLong_FromLong(self->bdd->OR(a, b));
}

static PyObject* PyROBDD_DIFF(PyROBDD* self, PyObject* args) {
    int a, b;
    if (!PyArg_ParseTuple(args, "ii", &a, &b)) return nullptr;
    return PyLong_FromLong(self->bdd->DIFF(a, b));
}

static PyObject* PyROBDD_size(PyROBDD* self, PyObject* /*args*/) {
    return PyLong_FromLong(self->bdd->size());
}

static PyObject* PyROBDD_top(PyROBDD* self, PyObject* args) {
    int n;
    if (!PyArg_ParseTuple(args, "i", &n)) return nullptr;
    return PyLong_FromLong(self->bdd->top(n));
}

static PyObject* PyROBDD_witness(PyROBDD* self, PyObject* args) {
    int node;
    if (!PyArg_ParseTuple(args, "i", &node)) return nullptr;
    auto result = self->bdd->witness(node);
    if (!result.has_value()) {
        Py_RETURN_NONE;
    }
    PyObject* dict = PyDict_New();
    for (auto& [k, v] : result.value()) {
        PyObject* key = PyLong_FromLong(k);
        PyObject* val = PyLong_FromLong(v);
        PyDict_SetItem(dict, key, val);
        Py_DECREF(key);
        Py_DECREF(val);
    }
    return dict;
}

// Expose FALSE and TRUE as properties
static PyObject* PyROBDD_get_FALSE(PyROBDD* /*self*/, void* /*closure*/) {
    return PyLong_FromLong(ROBDD::FALSE_ID);
}

static PyObject* PyROBDD_get_TRUE(PyROBDD* /*self*/, void* /*closure*/) {
    return PyLong_FromLong(ROBDD::TRUE_ID);
}

static PyMethodDef PyROBDD_methods[] = {
    {"var",     (PyCFunction)PyROBDD_var,     METH_VARARGS, "Create variable node for wire i"},
    {"AND",     (PyCFunction)PyROBDD_AND,     METH_VARARGS, "Conjunction of two nodes"},
    {"OR",      (PyCFunction)PyROBDD_OR,      METH_VARARGS, "Disjunction of two nodes"},
    {"DIFF",    (PyCFunction)PyROBDD_DIFF,    METH_VARARGS, "a AND NOT b"},
    {"size",    (PyCFunction)PyROBDD_size,    METH_NOARGS,  "Number of non-terminal nodes"},
    {"top",     (PyCFunction)PyROBDD_top,     METH_VARARGS, "Top variable of a node"},
    {"witness", (PyCFunction)PyROBDD_witness, METH_VARARGS, "Satisfying assignment or None"},
    {nullptr}
};

static PyGetSetDef PyROBDD_getset[] = {
    {"FALSE", (getter)PyROBDD_get_FALSE, nullptr, "False terminal node ID", nullptr},
    {"TRUE",  (getter)PyROBDD_get_TRUE,  nullptr, "True terminal node ID",  nullptr},
    {nullptr}
};

static PyTypeObject PyROBDD_Type = {
    .ob_base = PyVarObject_HEAD_INIT(nullptr, 0)
    .tp_name = "pyrobdd.ROBDD",
    .tp_basicsize = sizeof(PyROBDD),
    .tp_dealloc = (destructor)PyROBDD_dealloc,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_doc = "C++ ROBDD — drop-in replacement for order_only.py's ROBDD",
    .tp_methods = PyROBDD_methods,
    .tp_getset = PyROBDD_getset,
    .tp_init = (initproc)PyROBDD_init,
    .tp_new = PyType_GenericNew,
};

// ============================================================
// Module-level verify_sorts function
// ============================================================

static PyObject* py_verify_sorts(PyObject* /*self*/, PyObject* args) {
    int n;
    PyObject* comparators_list;
    if (!PyArg_ParseTuple(args, "iO", &n, &comparators_list)) return nullptr;

    if (!PyList_Check(comparators_list) && !PyTuple_Check(comparators_list)) {
        PyErr_SetString(PyExc_TypeError, "comparators must be a list or tuple of (i,j) pairs");
        return nullptr;
    }

    Py_ssize_t len = PySequence_Size(comparators_list);
    std::vector<std::pair<int, int>> comps;
    comps.reserve(len);

    for (Py_ssize_t idx = 0; idx < len; ++idx) {
        PyObject* pair = PySequence_GetItem(comparators_list, idx);
        if (!pair) return nullptr;

        int lo, hi;
        // Handle both tuples (i,j) and lists [i,j]
        if (PySequence_Size(pair) == 2) {
            PyObject* a = PySequence_GetItem(pair, 0);
            PyObject* b = PySequence_GetItem(pair, 1);
            if (!a || !b) {
                Py_XDECREF(a);
                Py_XDECREF(b);
                Py_DECREF(pair);
                return nullptr;
            }
            lo = PyLong_AsLong(a);
            hi = PyLong_AsLong(b);
            Py_DECREF(a);
            Py_DECREF(b);
            if (PyErr_Occurred()) { Py_DECREF(pair); return nullptr; }
        } else {
            Py_DECREF(pair);
            PyErr_SetString(PyExc_TypeError, "each comparator must be a 2-element sequence");
            return nullptr;
        }
        Py_DECREF(pair);
        comps.push_back({lo, hi});
    }

    bool result = ruachtov::verify_sorts(n, comps);
    return PyBool_FromLong(result);
}

// ============================================================
// Module definition
// ============================================================

static PyMethodDef module_methods[] = {
    {"verify_sorts", py_verify_sorts, METH_VARARGS,
     "Verify that a sorting network sorts all inputs.\n"
     "Args: n (int), comparators (list of (i,j) tuples)\n"
     "Returns: True if the network sorts."},
    {nullptr}
};

static struct PyModuleDef pyrobdd_module = {
    PyModuleDef_HEAD_INIT,
    "pyrobdd",
    "C++ ROBDD backend for sorting network verification.\n"
    "Drop-in replacement for order_only.py's ROBDD class.\n"
    "Ruach Tov Collective, 2026.",
    -1,
    module_methods,
};

PyMODINIT_FUNC PyInit_pyrobdd(void) {
    if (PyType_Ready(&PyROBDD_Type) < 0) return nullptr;

    PyObject* m = PyModule_Create(&pyrobdd_module);
    if (!m) return nullptr;

    Py_INCREF(&PyROBDD_Type);
    if (PyModule_AddObject(m, "ROBDD", (PyObject*)&PyROBDD_Type) < 0) {
        Py_DECREF(&PyROBDD_Type);
        Py_DECREF(m);
        return nullptr;
    }

    return m;
}
