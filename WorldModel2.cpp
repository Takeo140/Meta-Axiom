License Apache 2.0  Takeo Yamamoto
// UHA-WorldModel Core v1
//
// Semantic World Model
//        |
//      encode
//        v
// UHA Computational Core
//        |
//    transition
//        v
// encoded next world state
//
// No floating point.
// Deterministic.
// Exact modulo-2^64 arithmetic.

#include <array>
#include <cstdint>
#include <iostream>
#include <cassert>

namespace WorldModel {

// ============================================================
// 1. UHA BASE
// ============================================================

using U64 = std::uint64_t;

template <std::size_t N>
using UHAState = std::array<U64, N>;


// ============================================================
// 2. UHA UPDATE
// ============================================================

template <std::size_t N, class F>
constexpr UHAState<N>
UHAUpdate(
    const std::array<bool, N>& active,
    const F& f,
    const UHAState<N>& x)
{
    UHAState<N> out = x;

    for (std::size_t i = 0; i < N; ++i) {
        if (active[i]) {
            // Unsigned arithmetic is modulo 2^64.
            out[i] = x[i] + (f(x, i) - x[i]);
        }
    }

    return out;
}


// ============================================================
// 3. QUADRATIC UHA MAP
// ============================================================

template <std::size_t N>
struct QuadraticMap {

    constexpr U64 operator()(
        const UHAState<N>& x,
        std::size_t i) const noexcept
    {
        return x[i] * x[i];
    }
};


template <std::size_t N>
constexpr UHAState<N>
UHAQuadraticUpdate(
    const std::array<bool, N>& active,
    const UHAState<N>& x)
{
    return UHAUpdate<N>(
        active,
        QuadraticMap<N>{},
        x
    );
}


// ============================================================
// 4. FIXED POINT
// ============================================================

template <std::size_t N>
constexpr bool
isFixedPoint(
    const UHAState<N>& x,
    const UHAState<N>& next)
{
    return x == next;
}


// ============================================================
// 5. UHA COMPUTATIONAL KERNEL
// ============================================================

template <std::size_t N>
class UHAComputationalKernel {
public:

    using State = UHAState<N>;

    explicit constexpr
    UHAComputationalKernel(
        std::array<bool, N> active)
        : active_(active)
    {}

    constexpr State
    transition(const State& x) const noexcept
    {
        return UHAQuadraticUpdate<N>(
            active_,
            x
        );
    }

    constexpr bool
    fixedPoint(const State& x) const noexcept
    {
        return transition(x) == x;
    }

    constexpr const std::array<bool, N>&
    active() const noexcept
    {
        return active_;
    }

private:

    std::array<bool, N> active_;
};


// ============================================================
// 6. SEMANTIC PHYSICAL WORLD
// ============================================================

struct PhysicalState {

    U64 position;
    U64 velocity;
    U64 energy;
};


// Semantic world transition.
constexpr PhysicalState
physicalTransition(
    const PhysicalState& s) noexcept
{
    return PhysicalState{
        s.position + s.velocity,
        s.velocity,
        s.energy
    };
}


// ============================================================
// 7. WORLD ENCODING
// ============================================================

constexpr UHAState<3>
encode(
    const PhysicalState& s) noexcept
{
    return UHAState<3>{
        s.position,
        s.velocity,
        s.energy
    };
}


// ============================================================
// 8. WORLD MODEL
// ============================================================

template <std::size_t N>
class WorldModel {
public:

    using State = UHAState<N>;

    using SemanticState = PhysicalState;

    explicit constexpr
    WorldModel(
        UHAComputationalKernel<N> kernel)
        : kernel_(kernel)
    {}

    constexpr State
    encode(
        const SemanticState& s) const noexcept
    {
        static_assert(
            N == 3,
            "PhysicalState encoding requires N == 3"
        );

        return {
            s.position,
            s.velocity,
            s.energy
        };
    }

    constexpr SemanticState
    worldTransition(
        const SemanticState& s) const noexcept
    {
        return physicalTransition(s);
    }

    constexpr State
    computationalTransition(
        const State& x) const noexcept
    {
        return kernel_.transition(x);
    }

    constexpr const UHAComputationalKernel<N>&
    kernel() const noexcept
    {
        return kernel_;
    }

private:

    UHAComputationalKernel<N> kernel_;
};


// ============================================================
// 9. SEMANTIC WORLD STEP
// ============================================================

template <std::size_t N>
constexpr PhysicalState
worldStep(
    const WorldModel<N>& world,
    const PhysicalState& s) noexcept
{
    return world.worldTransition(s);
}


// ============================================================
// 10. COMPUTATIONAL WORLD STEP
// ============================================================

template <std::size_t N>
constexpr UHAState<N>
computationalStep(
    const WorldModel<N>& world,
    const PhysicalState& s) noexcept
{
    return world.computationalTransition(
        world.encode(s)
    );
}


// ============================================================
// 11. ENCODED SEMANTIC STEP
// ============================================================

template <std::size_t N>
constexpr UHAState<N>
encodedWorldStep(
    const WorldModel<N>& world,
    const PhysicalState& s) noexcept
{
    return world.encode(
        world.worldTransition(s)
    );
}


// ============================================================
// 12. WORLD/UHA COMMUTATION
// ============================================================
//
// Fundamental correspondence:
//
//   UHA(encode(s))
//       =
//   encode(WorldTransition(s))
//
// ============================================================

template <std::size_t N>
constexpr bool
transitionCommutes(
    const WorldModel<N>& world,
    const PhysicalState& s) noexcept
{
    return computationalStep(world, s)
        ==
           encodedWorldStep(world, s);
}


// ============================================================
// 13. WORLD FIXED POINT
// ============================================================

template <std::size_t N>
constexpr bool
worldFixedPoint(
    const WorldModel<N>& world,
    const PhysicalState& s) noexcept
{
    const auto x = world.encode(s);

    return world.kernel().fixedPoint(x);
}


// ============================================================
// 14. UNIFIED WORLD STATE
// ============================================================

template <std::size_t N>
struct UnifiedWorldState {

    PhysicalState semantic;

    UHAState<N> computational;

    constexpr bool coherent(
        const WorldModel<N>& world) const noexcept
    {
        return computational == world.encode(semantic);
    }
};


// ============================================================
// 15. F-THEORY LAYER
// ============================================================

template <class S>
struct MetaAxiom {

    bool (*holds)(const S&);
};


template <class S>
struct PhysicalLaw {

    bool (*holds)(const S&);
};


template <std::size_t N>
struct FTheoryWorld {

    MetaAxiom<PhysicalState> meta;

    PhysicalLaw<PhysicalState> law;

    WorldModel<N> model;
};


// ============================================================
// 16. EXAMPLE AXIOM / LAW
// ============================================================

constexpr bool
energyNonNegative(
    const PhysicalState&)
{
    // U64 representation is inherently non-negative.
    return true;
}


constexpr bool
basicPhysicalLaw(
    const PhysicalState&)
{
    return true;
}


// ============================================================
// 17. TESTS
// ============================================================

void runTests()
{
    // All three components active.
    constexpr UHAComputationalKernel<3> kernel(
        std::array<bool, 3>{
            true,
            true,
            true
        }
    );

    constexpr WorldModel<3> world(kernel);

    constexpr PhysicalState initial{
        3,
        4,
        100
    };

    // --------------------------------------------------------
    // Encoding
    // --------------------------------------------------------

    constexpr auto encoded =
        world.encode(initial);

    static_assert(encoded[0] == 3);
    static_assert(encoded[1] == 4);
    static_assert(encoded[2] == 100);


    // --------------------------------------------------------
    // Semantic transition
    // --------------------------------------------------------

    constexpr auto semanticNext =
        world.worldTransition(initial);

    static_assert(
        semanticNext.position == 7
    );

    static_assert(
        semanticNext.velocity == 4
    );

    static_assert(
        semanticNext.energy == 100
    );


    // --------------------------------------------------------
    // Fundamental correspondence
    // --------------------------------------------------------

    //
    // NOTE:
    //
    // The quadratic UHA kernel does NOT reproduce the
    // physicalTransition above:
    //
    //   3 -> 9
    //   4 -> 16
    //
    // Therefore this test correctly exposes the fact that
    // an arbitrary semantic transition cannot simply be
    // declared equivalent to the quadratic UHA kernel.
    //
    // The production architecture therefore requires the
    // WorldModel computational transition to be the actual
    // encoded semantic transition, or a proven equivalent
    // UHA map.
    //
}


// ============================================================
// 18. EXACT SEMANTIC UHA KERNEL
// ============================================================
//
// This is the implementation that actually satisfies:
//
//     computationalTransition(encode(s))
//       =
//     encode(worldTransition(s))
//
// ============================================================

class PhysicalUHAKernel {

public:

    using State = UHAState<3>;

    constexpr State
    transition(const State& x) const noexcept
    {
        return State{
            x[0] + x[1],
            x[1],
            x[2]
        };
    }

    constexpr bool
    fixedPoint(const State& x) const noexcept
    {
        return transition(x) == x;
    }
};


// ============================================================
// 19. CORRECT WORLD MODEL
// ============================================================

class PhysicalWorldModel {

public:

    using State = UHAState<3>;

    constexpr State
    encode(
        const PhysicalState& s) const noexcept
    {
        return {
            s.position,
            s.velocity,
            s.energy
        };
    }

    constexpr PhysicalState
    worldTransition(
        const PhysicalState& s) const noexcept
    {
        return {
            s.position + s.velocity,
            s.velocity,
            s.energy
        };
    }

    constexpr State
    computationalTransition(
        const State& x) const noexcept
    {
        return {
            x[0] + x[1],
            x[1],
            x[2]
        };
    }

    constexpr bool
    transitionCommutes(
        const PhysicalState& s) const noexcept
    {
        return
            computationalTransition(encode(s))
            ==
            encode(worldTransition(s));
    }
};


// ============================================================
// 20. MAIN
// ============================================================

int main()
{
    PhysicalWorldModel world;

    PhysicalState s{
        10,
        5,
        100
    };

    auto x =
        world.encode(s);

    auto next =
        world.computationalTransition(x);

    auto semantic =
        world.worldTransition(s);

    assert(
        world.transitionCommutes(s)
    );

    assert(
        next == world.encode(semantic)
    );

    std::cout
        << "UHA-WorldModel Core: OK\n";

    std::cout
        << "position: "
        << next[0]
        << '\n';

    std::cout
        << "velocity: "
        << next[1]
        << '\n';

    std::cout
        << "energy: "
        << next[2]
        << '\n';

    return 0;
}
