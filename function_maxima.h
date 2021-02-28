#ifndef MAXIMA_H
#define MAXIMA_H

#include <set>
#include <exception>
#include <utility>
#include <memory>
#include <iterator>
#include <cstddef>
#include <vector>

class InvalidArg : public std::exception {
public:
    const char *what() const noexcept override {
        return "invalid argument value";
    }
};

template<typename A, typename V>
class FunctionMaxima {
private:
    class point;

    struct comp_by_arg;
    struct comp_by_maxima;
    using func_t = std::multiset<point, comp_by_arg>;
    using maxima_t = std::multiset<point, comp_by_maxima>;

public:
    using size_type = std::size_t;
    using point_type = point;
    using iterator = typename func_t::const_iterator;
    using mx_iterator = typename maxima_t::const_iterator;

    V const &value_at(A const &a) const {
        iterator it = function.find(a);
        if (it == end())
            throw InvalidArg();

        return it->value();
    }

    void erase(A const &a) {
        std::vector <mx_iterator> maxima_rollback;
        iterator it = end();
        mx_iterator max_it = mx_end();
        try {
            it = function.find(a); // O(log(n))
            if (it == end()) {
                return;
            }
            max_it = maxima.find(*it); // O(log(k))
            update_maxima(it, it, maxima_rollback); //O(log(k))
        } catch (...) {
            for (const auto &iter : maxima_rollback) {
                maxima.erase(iter);
            }
            throw;
        }
        function.erase(it); // O(1) (amortized)
        if (max_it != mx_end()) {
            maxima.erase(max_it); // O(1) (amortized)
        }
    }

    void set_value(A const &a, V const &v) {
        iterator it = end(), prev_it = end();
        mx_iterator prev_max_it = mx_end();
        std::vector <mx_iterator> maxima_rollback;
        bool diff;
        try {
            point_type new_point(a, v);
            prev_it = function.lower_bound(a); // O(log(n))
            if (prev_it != end()) {
                prev_max_it = maxima.find(*prev_it); // O(log(k))
            }
            it = function.insert(prev_it, new_point); // O(1) (amortized)
            diff = prev_it != end() && !function.key_comp()(*it, *prev_it);
            update_maxima(it, diff ? prev_it : end(), maxima_rollback); // O(log(n))
        } catch (...) {
            for (const auto &max_it : maxima_rollback) {
                maxima.erase(max_it);
            }
            if (it != end()) {
                function.erase(it);
            }
            throw;
        }
        if (diff) {
            if (prev_max_it != mx_end()) {
                maxima.erase(prev_max_it); // O(1) (amortized)
            }
            function.erase(prev_it); // O(1) (amortized)

        }
    }

    size_type size() const noexcept {
        return function.size();
    };

    iterator begin() const noexcept {
        return function.cbegin();
    }

    iterator end() const noexcept {
        return function.cend();
    }

    iterator find(A const &a) const {
        return function.find(a);
    }

    mx_iterator mx_begin() const noexcept {
        return maxima.cbegin();
    }

    mx_iterator mx_end() const noexcept {
        return maxima.cend();
    }

    FunctionMaxima() = default;

    FunctionMaxima(const FunctionMaxima &fun) = default;

    FunctionMaxima &operator=(const FunctionMaxima &fun) {
        if (this != &fun) {
            auto temp_fun = fun.function;
            auto temp_max = fun.maxima;
            function.swap(temp_fun);
            maxima.swap(temp_max);
        }
        return *this;
    }

private:
    func_t function;
    maxima_t maxima;

    class point {
    public:
        A const &arg() const {
            return *_arg;
        }

        V const &value() const {
            return *_value;
        }

    private:
        friend class FunctionMaxima;

        std::shared_ptr <A> _arg;
        std::shared_ptr <V> _value;

        point(const A &a, const V &v) :
                _arg(std::make_shared<A>(a)),
                _value(std::make_shared<V>(v)) {}

    };

    struct comp_by_arg {
        // flag enables comparing diferrent types than just template arguments of the set.
        using is_transparent = std::true_type;

        bool operator()(const point_type &p1, const point_type &p2) const {
            return p1.arg() < p2.arg();
        }

        bool operator()(const point_type &p, const A &a) const {
            return p.arg() < a;
        }

        bool operator()(const A &a, const point_type &p) const {
            return a < p.arg();
        }
    };

    struct comp_by_maxima {
        bool operator()(point_type p1, point_type p2) const {
            return p2.value() < p1.value() || (!(p1.value() < p2.value()) && (p1.arg() < p2.arg()));
        }
    };


    bool is_local_maximum(iterator it, iterator omit_it) {
        if (it == omit_it)
            return false;

        iterator cpy_it = it;
        if (it != begin()) {
            cpy_it--;
            if (cpy_it != omit_it) {
                if (it->value() < cpy_it->value()) {
                    return false;
                }
            } else if (cpy_it != begin()) {
                if (it->value() < (--cpy_it)->value()) {
                    return false;
                }
            }
        }

        cpy_it = it;

        if (++cpy_it != end()) {
            if (cpy_it != omit_it) {
                if (it->value() < cpy_it->value()) {
                    return false;
                }
            } else if ((++cpy_it) != end()) {
                if (it->value() < cpy_it->value()) {
                    return false;
                }
            }
        }
        return true;
    }

    /** Returns mx_iterator to *cpy_it iff *cpy_it ceased to be a local maximum.
      * Otherwise returns mx_end() */
    mx_iterator stopped_being_maximum(iterator cpy_it, iterator omit_it, std::vector <mx_iterator> &rollback) {
        mx_iterator res = maxima.find(*cpy_it);
        if (is_local_maximum(cpy_it, omit_it)) {
            if (res == mx_end()) {
                mx_iterator curr = maxima.insert(*cpy_it);
                rollback.push_back(curr);
            }
            return mx_end();
        }
        return res;
    }

    /** Decrements it if it is possible. Returns true if it has been decremented,
      * and false therwise. */
    bool safe_decrement(iterator &it) {
        return (it == begin()) ? false : (it--, true);
    }


    void update_maxima(iterator it, iterator omit_it, std::vector <mx_iterator> &rollback) {
        iterator cpy_it = it;
        mx_iterator left = mx_end(), right = mx_end();

        if (is_local_maximum(it, omit_it)) {
            mx_iterator curr = maxima.insert(*it);
            rollback.push_back(curr);
        }

        if (safe_decrement(cpy_it)) {
            if (cpy_it != omit_it || safe_decrement(cpy_it)) {
                left = stopped_being_maximum(cpy_it, omit_it, rollback);
            }
        }

        cpy_it = it;

        if (++cpy_it != end()) {
            if (cpy_it != omit_it || ++cpy_it != end()) {
                right = stopped_being_maximum(cpy_it, omit_it, rollback);
            }
        }

        if (left != mx_end()) {
            maxima.erase(left);
        }

        if (right != mx_end()) {
            maxima.erase(right);
        }

    }
};


#endif