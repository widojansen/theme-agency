function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}
function null_to_empty(value) {
    return value == null ? '' : value;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let style;
	let t;

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			style = element("style");
			t = text("/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: rebeccapurple;\n\n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #cbcace;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: white;\n  line-height: 1.2;\n  font-size: 1.125rem;\n  background: black;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1300px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n  font-weight: 400;\n  border-bottom: 2px solid;\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: clamp(2rem,10vw, 3rem);\n  font-weight: 500;\n  line-height: 1.3;\n}\n\n.button {\n  color: #111;\n  font-size: 1rem;\n  background: white;\n  border-radius: 2rem;\n  padding: 18px 28px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.is-inverted {\n    background: black;\n    color: white;\n  }\n\n/* Content Section */\n.content { \n  max-width: 1300px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n  line-height: 1.4;\n  font-size: 2rem;\n}\n.content > * {\n    max-width: 600px;\n  }\n.content p {\n    padding: 0.25rem 0;\n  }\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content a.link {\n  }\n.content h1 {\n    font-size: 3.5rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n.content h3 {\n    font-size: 1.75rem;\n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content h1 {\n    padding-top: 10rem;\n    max-width: 800px;\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1funr7q', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: rebeccapurple;\n\n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #cbcace;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: white;\n  line-height: 1.2;\n  font-size: 1.125rem;\n  background: black;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1300px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n  font-weight: 400;\n  border-bottom: 2px solid;\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: clamp(2rem,10vw, 3rem);\n  font-weight: 500;\n  line-height: 1.3;\n}\n\n.button {\n  color: #111;\n  font-size: 1rem;\n  background: white;\n  border-radius: 2rem;\n  padding: 18px 28px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.is-inverted {\n    background: black;\n    color: white;\n  }\n\n/* Content Section */\n.content { \n  max-width: 1300px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n  line-height: 1.4;\n  font-size: 2rem;\n}\n.content > * {\n    max-width: 600px;\n  }\n.content p {\n    padding: 0.25rem 0;\n  }\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content a.link {\n  }\n.content h1 {\n    font-size: 3.5rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n.content h3 {\n    font-size: 1.75rem;\n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content h1 {\n    padding-top: 10rem;\n    max-width: 800px;\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { footer_links } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('footer_links' in $$props) $$invalidate(2, footer_links = $$props.footer_links);
	};

	return [logo, site_nav, footer_links];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { logo: 0, site_nav: 1, footer_links: 2 });
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].link;
	return child_ctx;
}

// (106:31) 
function create_if_block_4(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (104:6) {#if logo.title}
function create_if_block_3(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (111:6) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[7].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-sip8mq");
			attr(a, "href", a_href_value = /*link*/ ctx[7].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[7].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[7].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (120:31) 
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (118:6) {#if logo.title}
function create_if_block_1$1(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (130:4) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let t;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-sip8mq");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-sip8mq");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[5]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2) {
				each_value = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (132:8) {#each site_nav as { link }}
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[7].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "mobile-link");
			attr(a, "href", a_href_value = /*link*/ ctx[7].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[7].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[7].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$2(ctx) {
	let div3;
	let div2;
	let header;
	let div0;
	let a0;
	let t0;
	let nav;
	let t1;
	let div1;
	let a1;
	let t2;
	let button;
	let icon;
	let t3;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_3;
		if (/*logo*/ ctx[0].image.url) return create_if_block_4;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type && current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_1$1;
		if (/*logo*/ ctx[0].image.url) return create_if_block_2;
	}

	let current_block_type_1 = select_block_type_1(ctx);
	let if_block1 = current_block_type_1 && current_block_type_1(ctx);

	icon = new Component$1({
			props: { height: "30", icon: "eva:menu-outline" }
		});

	let if_block2 = /*mobileNavOpen*/ ctx[2] && create_if_block$1(ctx);

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			header = element("header");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			div1 = element("div");
			a1 = element("a");
			if (if_block1) if_block1.c();
			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t3 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a1 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			if (if_block1) if_block1.l(a1_nodes);
			a1_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-sip8mq");
			attr(nav, "class", "svelte-sip8mq");
			attr(div0, "class", "desktop-nav svelte-sip8mq");
			attr(a1, "href", "/");
			attr(a1, "class", "logo svelte-sip8mq");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-sip8mq");
			attr(header, "class", "section-container svelte-sip8mq");
			attr(div2, "class", "component");
			attr(div3, "class", "section");
			attr(div3, "id", "section-4ad32027-b1a8-4fae-b9d5-e81b9a7ab8d5");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, header);
			append_hydration(header, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(header, t1);
			append_hydration(header, div1);
			append_hydration(div1, a1);
			if (if_block1) if_block1.m(a1, null);
			append_hydration(div1, t2);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t3);
			if (if_block2) if_block2.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[4]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if (if_block0) if_block0.d(1);
				if_block0 = current_block_type && current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a0, null);
				}
			}

			if (dirty & /*site_nav*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if (current_block_type_1 === (current_block_type_1 = select_block_type_1(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if (if_block1) if_block1.d(1);
				if_block1 = current_block_type_1 && current_block_type_1(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(a1, null);
				}
			}

			if (/*mobileNavOpen*/ ctx[2]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 4) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$1(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);

			if (if_block0) {
				if_block0.d();
			}

			destroy_each(each_blocks, detaching);

			if (if_block1) {
				if_block1.d();
			}

			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { footer_links } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(2, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(2, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('footer_links' in $$props) $$invalidate(3, footer_links = $$props.footer_links);
	};

	return [logo, site_nav, mobileNavOpen, footer_links, click_handler, click_handler_1];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$2, create_fragment$2, safe_not_equal, { logo: 0, site_nav: 1, footer_links: 3 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$3(ctx) {
	let div2;
	let div1;
	let div0;
	let feature;
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			feature = element("feature");
			img = element("img");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			feature = claim_element(div0_nodes, "FEATURE", {});
			var feature_nodes = children(feature);
			img = claim_element(feature_nodes, "IMG", { src: true, alt: true, class: true });
			feature_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[0].alt);
			attr(img, "class", "svelte-w1hg46");
			attr(div0, "class", "section-container svelte-w1hg46");
			attr(div1, "class", "component");
			attr(div2, "class", "section");
			attr(div2, "id", "section-0715bb4c-8554-4dd3-8f67-2943d505a303");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			append_hydration(div0, feature);
			append_hydration(feature, img);
		},
		p(ctx, [dirty]) {
			if (dirty & /*image*/ 1 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 1 && img_alt_value !== (img_alt_value = /*image*/ ctx[0].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { footer_links } = $$props;
	let { image } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(1, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(2, site_nav = $$props.site_nav);
		if ('footer_links' in $$props) $$invalidate(3, footer_links = $$props.footer_links);
		if ('image' in $$props) $$invalidate(0, image = $$props.image);
	};

	return [image, logo, site_nav, footer_links];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			logo: 1,
			site_nav: 2,
			footer_links: 3,
			image: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$4(ctx) {
	let div1;
	let div0;
	let section;
	let h1;
	let t;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			section = element("section");
			h1 = element("h1");
			t = text(/*headline*/ ctx[0]);
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			section = claim_element(div0_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h1 = claim_element(section_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t = claim_text(h1_nodes, /*headline*/ ctx[0]);
			h1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "headline svelte-1au42aa");
			attr(section, "class", "section-container svelte-1au42aa");
			attr(div0, "class", "component");
			attr(div1, "class", "section");
			attr(div1, "id", "section-4ce7a0e6-9630-4d04-9843-3ada0db6e240");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, section);
			append_hydration(section, h1);
			append_hydration(h1, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*headline*/ 1) set_data(t, /*headline*/ ctx[0]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { footer_links } = $$props;
	let { headline } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(1, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(2, site_nav = $$props.site_nav);
		if ('footer_links' in $$props) $$invalidate(3, footer_links = $$props.footer_links);
		if ('headline' in $$props) $$invalidate(0, headline = $$props.headline);
	};

	return [headline, logo, site_nav, footer_links];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			logo: 1,
			site_nav: 2,
			footer_links: 3,
			headline: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$5(ctx) {
	let div2;
	let div1;
	let section;
	let div0;
	let raw_value = /*content*/ ctx[1].html + "";
	let t0;
	let a;
	let t1_value = /*link*/ ctx[0].label + "";
	let t1;
	let a_href_value;

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			t0 = space();
			a = element("a");
			t1 = text(t1_value);
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t0 = claim_space(section_nodes);
			a = claim_element(section_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t1 = claim_text(a_nodes, t1_value);
			a_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "content svelte-10e1ceb");
			attr(a, "href", a_href_value = /*link*/ ctx[0].url);
			attr(a, "class", "button");
			attr(section, "class", "section-container svelte-10e1ceb");
			attr(div1, "class", "component");
			attr(div2, "class", "section");
			attr(div2, "id", "section-48095eca-7e49-45f6-8ba4-510e94427c3f");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, section);
			append_hydration(section, div0);
			div0.innerHTML = raw_value;
			append_hydration(section, t0);
			append_hydration(section, a);
			append_hydration(a, t1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 2 && raw_value !== (raw_value = /*content*/ ctx[1].html + "")) div0.innerHTML = raw_value;			if (dirty & /*link*/ 1 && t1_value !== (t1_value = /*link*/ ctx[0].label + "")) set_data(t1, t1_value);

			if (dirty & /*link*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[0].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { footer_links } = $$props;
	let { heading } = $$props;
	let { link } = $$props;
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(2, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(3, site_nav = $$props.site_nav);
		if ('footer_links' in $$props) $$invalidate(4, footer_links = $$props.footer_links);
		if ('heading' in $$props) $$invalidate(5, heading = $$props.heading);
		if ('link' in $$props) $$invalidate(0, link = $$props.link);
		if ('content' in $$props) $$invalidate(1, content = $$props.content);
	};

	return [link, content, logo, site_nav, footer_links, heading];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			logo: 2,
			site_nav: 3,
			footer_links: 4,
			heading: 5,
			link: 0,
			content: 1
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$6(ctx) {
	let div2;
	let div1;
	let section;
	let div0;
	let h2;
	let t0;
	let t1;
	let a;
	let t2_value = /*link*/ ctx[1].label + "";
	let t2;
	let a_href_value;
	let section_class_value;

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			a = element("a");
			t2 = text(t2_value);
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			a = claim_element(div0_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t2 = claim_text(a_nodes, t2_value);
			a_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-157t201");
			attr(a, "href", a_href_value = /*link*/ ctx[1].url);
			attr(a, "class", "button");
			toggle_class(a, "is-inverted", /*variation*/ ctx[2] === 'light');
			attr(div0, "class", "section-container svelte-157t201");
			attr(section, "class", section_class_value = "" + (null_to_empty(/*variation*/ ctx[2]) + " svelte-157t201"));
			attr(div1, "class", "component");
			attr(div2, "class", "section");
			attr(div2, "id", "section-544bb491-664a-4f6d-ba65-0703d2b57a6b");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, section);
			append_hydration(section, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			append_hydration(div0, a);
			append_hydration(a, t2);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*link*/ 2 && t2_value !== (t2_value = /*link*/ ctx[1].label + "")) set_data(t2, t2_value);

			if (dirty & /*link*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[1].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*variation*/ 4) {
				toggle_class(a, "is-inverted", /*variation*/ ctx[2] === 'light');
			}

			if (dirty & /*variation*/ 4 && section_class_value !== (section_class_value = "" + (null_to_empty(/*variation*/ ctx[2]) + " svelte-157t201"))) {
				attr(section, "class", section_class_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { footer_links } = $$props;
	let { heading } = $$props;
	let { link } = $$props;
	let { variation } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(3, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(4, site_nav = $$props.site_nav);
		if ('footer_links' in $$props) $$invalidate(5, footer_links = $$props.footer_links);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('link' in $$props) $$invalidate(1, link = $$props.link);
		if ('variation' in $$props) $$invalidate(2, variation = $$props.variation);
	};

	return [heading, link, variation, logo, site_nav, footer_links];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$6, safe_not_equal, {
			logo: 3,
			site_nav: 4,
			footer_links: 5,
			heading: 0,
			link: 1,
			variation: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i].image;
	return child_ctx;
}

// (39:6) {#each items as {image}}
function create_each_block$1(ctx) {
	let div;
	let img;
	let img_src_value;
	let img_alt_value;
	let t;

	return {
		c() {
			div = element("div");
			img = element("img");
			t = space();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			img = claim_element(div_nodes, "IMG", { src: true, alt: true, class: true });
			t = claim_space(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[6].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[6].alt);
			attr(img, "class", "svelte-yapjk8");
			attr(div, "class", "item");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, img);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 2 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[6].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*items*/ 2 && img_alt_value !== (img_alt_value = /*image*/ ctx[6].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function create_fragment$7(ctx) {
	let div3;
	let div2;
	let section;
	let div1;
	let h2;
	let t0;
	let t1;
	let div0;
	let section_class_value;
	let each_value = /*items*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			section = element("section");
			div1 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-yapjk8");
			attr(div0, "class", "items svelte-yapjk8");
			attr(div1, "class", "section-container");
			attr(section, "class", section_class_value = "" + (null_to_empty(/*variation*/ ctx[2]) + " svelte-yapjk8"));
			attr(div2, "class", "component");
			attr(div3, "class", "section");
			attr(div3, "id", "section-e521e1dc-b6bb-4640-8740-7f10316ceb2f");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, section);
			append_hydration(section, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*items*/ 2) {
				each_value = /*items*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*variation*/ 4 && section_class_value !== (section_class_value = "" + (null_to_empty(/*variation*/ ctx[2]) + " svelte-yapjk8"))) {
				attr(section, "class", section_class_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { footer_links } = $$props;
	let { heading } = $$props;
	let { items } = $$props;
	let { variation } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(3, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(4, site_nav = $$props.site_nav);
		if ('footer_links' in $$props) $$invalidate(5, footer_links = $$props.footer_links);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('items' in $$props) $$invalidate(1, items = $$props.items);
		if ('variation' in $$props) $$invalidate(2, variation = $$props.variation);
	};

	return [heading, items, variation, logo, site_nav, footer_links];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$7, safe_not_equal, {
			logo: 3,
			site_nav: 4,
			footer_links: 5,
			heading: 0,
			items: 1,
			variation: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$8(ctx) {
	let div2;
	let div1;
	let section;
	let div0;
	let h2;
	let t0;
	let t1;
	let a;
	let t2_value = /*link*/ ctx[1].label + "";
	let t2;
	let a_href_value;
	let section_class_value;

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			a = element("a");
			t2 = text(t2_value);
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			a = claim_element(div0_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t2 = claim_text(a_nodes, t2_value);
			a_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-157t201");
			attr(a, "href", a_href_value = /*link*/ ctx[1].url);
			attr(a, "class", "button");
			toggle_class(a, "is-inverted", /*variation*/ ctx[2] === 'light');
			attr(div0, "class", "section-container svelte-157t201");
			attr(section, "class", section_class_value = "" + (null_to_empty(/*variation*/ ctx[2]) + " svelte-157t201"));
			attr(div1, "class", "component");
			attr(div2, "class", "section");
			attr(div2, "id", "section-f6aa0103-2811-4baa-b6e4-c1f6b179b816");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, section);
			append_hydration(section, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			append_hydration(div0, a);
			append_hydration(a, t2);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*link*/ 2 && t2_value !== (t2_value = /*link*/ ctx[1].label + "")) set_data(t2, t2_value);

			if (dirty & /*link*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[1].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*variation*/ 4) {
				toggle_class(a, "is-inverted", /*variation*/ ctx[2] === 'light');
			}

			if (dirty & /*variation*/ 4 && section_class_value !== (section_class_value = "" + (null_to_empty(/*variation*/ ctx[2]) + " svelte-157t201"))) {
				attr(section, "class", section_class_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$8($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { footer_links } = $$props;
	let { heading } = $$props;
	let { link } = $$props;
	let { variation } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(3, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(4, site_nav = $$props.site_nav);
		if ('footer_links' in $$props) $$invalidate(5, footer_links = $$props.footer_links);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('link' in $$props) $$invalidate(1, link = $$props.link);
		if ('variation' in $$props) $$invalidate(2, variation = $$props.variation);
	};

	return [heading, link, variation, logo, site_nav, footer_links];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$8, create_fragment$8, safe_not_equal, {
			logo: 3,
			site_nav: 4,
			footer_links: 5,
			heading: 0,
			link: 1,
			variation: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	return child_ctx;
}

// (29:4) {#each footer_links as { link }}
function create_each_block$2(ctx) {
	let a;
	let t_value = /*link*/ ctx[3].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link");
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*footer_links*/ 1 && t_value !== (t_value = /*link*/ ctx[3].label + "")) set_data(t, t_value);

			if (dirty & /*footer_links*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$9(ctx) {
	let div1;
	let div0;
	let footer;
	let nav;
	let t0;
	let span;
	let t1;
	let a;
	let t2;
	let each_value = /*footer_links*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			footer = element("footer");
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			span = element("span");
			t1 = text("Powered by\n    ");
			a = element("a");
			t2 = text("Primo");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			footer = claim_element(div0_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			nav = claim_element(footer_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			t0 = claim_space(footer_nodes);
			span = claim_element(footer_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, "Powered by\n    ");
			a = claim_element(span_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t2 = claim_text(a_nodes, "Primo");
			a_nodes.forEach(detach);
			span_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav, "class", "svelte-1n8xi4a");
			attr(a, "href", "https://primo.so");
			attr(a, "class", "primo svelte-1n8xi4a");
			attr(span, "class", "primo svelte-1n8xi4a");
			attr(footer, "class", "section-container svelte-1n8xi4a");
			attr(div0, "class", "component");
			attr(div1, "class", "section");
			attr(div1, "id", "section-94e9263d-db7c-4dc4-b2a4-e320ece6151f");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, footer);
			append_hydration(footer, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(footer, t0);
			append_hydration(footer, span);
			append_hydration(span, t1);
			append_hydration(span, a);
			append_hydration(a, t2);
		},
		p(ctx, [dirty]) {
			if (dirty & /*footer_links*/ 1) {
				each_value = /*footer_links*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$9($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { footer_links } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(1, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(2, site_nav = $$props.site_nav);
		if ('footer_links' in $$props) $$invalidate(0, footer_links = $$props.footer_links);
	};

	return [footer_links, logo, site_nav];
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$9, create_fragment$9, safe_not_equal, { logo: 1, site_nav: 2, footer_links: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function instance$a($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { footer_links } = $$props;

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('footer_links' in $$props) $$invalidate(2, footer_links = $$props.footer_links);
	};

	return [logo, site_nav, footer_links];
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$a, null, safe_not_equal, { logo: 0, site_nav: 1, footer_links: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$a(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let t6;
	let component_7;
	let t7;
	let component_8;
	let t8;
	let component_9;
	let current;

	component_0 = new Component({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Prolan & Co"
				},
				site_nav: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				footer_links: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact Us" }
					}
				]
			}
		});

	component_1 = new Component$2({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Prolan & Co"
				},
				site_nav: [
					{
						"link": {
							"url": "/work",
							"label": "Work",
							"active": false
						}
					},
					{
						"link": {
							"url": "/services",
							"label": "Services",
							"active": false
						}
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				footer_links: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact Us" }
					}
				]
			}
		});

	component_2 = new Component$3({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Prolan & Co"
				},
				site_nav: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				footer_links: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact Us" }
					}
				],
				image: {
					"alt": "",
					"src": "https://images.unsplash.com/photo-1479030160180-b1860951d696?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2070&q=80",
					"url": "https://images.unsplash.com/photo-1479030160180-b1860951d696?ixlib=rb-4.0.3&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=2070&q=80",
					"size": null
				}
			}
		});

	component_3 = new Component$4({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Prolan & Co"
				},
				site_nav: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				footer_links: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact Us" }
					}
				],
				headline: "Prolan & Co is a digital product agency that focuses on strategy and design inspired by nature."
			}
		});

	component_4 = new Component$5({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Prolan & Co"
				},
				site_nav: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				footer_links: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact Us" }
					}
				],
				heading: "Non est nostrud",
				link: {
					"url": "/services",
					"label": "Our Services"
				},
				content: {
					"html": "<p>Exercitation aliquip cillum consequat consectetur officia. Nostrud deserunt et labore sit. </p>",
					"markdown": "Exercitation aliquip cillum consequat consectetur officia. Nostrud deserunt et labore sit.\n\n"
				}
			}
		});

	component_5 = new Component$6({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Prolan & Co"
				},
				site_nav: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				footer_links: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact Us" }
					}
				],
				heading: "We've done good work with good people, for good people",
				link: { "url": "/work", "label": "View our work" },
				variation: "light"
			}
		});

	component_6 = new Component$7({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Prolan & Co"
				},
				site_nav: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				footer_links: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact Us" }
					}
				],
				heading: "Who we've worked with",
				items: [
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-75' width='186' height='41' viewBox='0 0 186 41' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M59.0372 2.72868C59.0372 1.33929 60.1758 0.212959 61.5805 0.212959H66.0111C67.0108 0.212959 67.9797 0.555658 68.7527 1.18272L70.1005 2.276L70.1342 2.30641C70.1653 2.29603 70.1964 2.28589 70.2276 2.276C72.6592 1.50561 75.6094 1.3591 78.6205 1.3591C81.6316 1.3591 84.5818 1.50561 87.0134 2.276C87.0446 2.28589 87.0757 2.29603 87.1068 2.30641L87.1405 2.276L88.4883 1.18272C89.2613 0.555658 90.2302 0.212959 91.2299 0.212959H95.6605C97.0652 0.212959 98.2038 1.33929 98.2038 2.72868V4.28386C98.2038 5.48711 97.6914 6.6347 96.7922 7.4451L95.7049 8.42509C95.1741 8.90351 94.537 9.25169 93.845 9.44151L93.5878 9.51207C94.5953 11.89 95.1519 14.4318 95.1519 16.488C95.1519 24.7594 89.978 28.3317 85.4192 31.4793C81.8291 33.9581 78.6205 36.1734 78.6205 40.213C78.6205 36.1734 75.4119 33.9581 71.8218 31.4793C67.263 28.3317 62.0891 24.7594 62.0891 16.488C62.0891 14.4318 62.6457 11.89 63.6532 9.51207L63.396 9.44151C62.704 9.25169 62.0669 8.90351 61.5361 8.42509L60.4488 7.4451C59.5496 6.6347 59.0372 5.48711 59.0372 4.28386V2.72868ZM81.9268 23.2502C81.9268 23.6454 81.7526 24.0243 81.4426 24.3038C81.1326 24.5832 80.7121 24.7402 80.2736 24.7402C79.8951 24.7402 79.5299 24.6231 79.2377 24.4113C79.7351 25.7283 81.008 26.9762 82.9441 24.9694C84.6533 23.1047 82.8681 19.1718 81.1289 16.838C80.5492 16.0601 79.5975 15.6857 78.6205 15.6857C77.6435 15.6857 76.6918 16.0601 76.1121 16.838C74.3729 19.1718 72.5877 23.1047 74.2969 24.9694C76.233 26.9762 77.5059 25.7283 78.0033 24.4113C77.7111 24.6231 77.3459 24.7402 76.9674 24.7402C76.5289 24.7402 76.1084 24.5832 75.7984 24.3038C75.4884 24.0243 75.3142 23.6454 75.3142 23.2502H81.9268ZM72.2898 11.6081H67.6844L71.3139 14.4828C72.1126 15.1153 73.28 14.9131 73.7742 14.0566C74.3982 12.9752 73.5694 11.6081 72.2898 11.6081ZM84.9512 11.6081H89.5566L85.9271 14.4828C85.1284 15.1153 83.961 14.9131 83.4668 14.0566C82.8428 12.9752 83.6716 11.6081 84.9512 11.6081Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M103.69 28.5463H107.77V13.1563H103.69V28.5463ZM103.69 10.7563H107.77V7.09629H103.69V10.7563Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M110.399 33.5863H114.479V26.8063H114.539C115.409 28.1263 116.819 28.9963 118.979 28.9963C122.939 28.9963 125.639 25.8463 125.639 20.8663C125.639 16.0663 123.029 12.7363 118.949 12.7363C116.849 12.7363 115.409 13.7263 114.419 15.0763H114.329V13.1563H110.399V33.5863ZM118.109 25.6063C115.679 25.6063 114.389 23.7763 114.389 20.9863C114.389 18.2263 115.409 16.0363 117.959 16.0363C120.479 16.0363 121.499 18.0763 121.499 20.9863C121.499 23.8963 120.179 25.6063 118.109 25.6063Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M133.778 28.9963C137.618 28.9963 140.258 27.1363 140.258 24.0463C140.258 20.4463 137.408 19.7263 134.828 19.1863C132.638 18.7363 130.598 18.6163 130.598 17.2963C130.598 16.1863 131.648 15.5863 133.238 15.5863C134.978 15.5863 136.028 16.1863 136.208 17.8363H139.898C139.598 14.7463 137.348 12.7363 133.298 12.7363C129.788 12.7363 127.028 14.3263 127.028 17.6563C127.028 21.0163 129.728 21.7663 132.488 22.3063C134.588 22.7263 136.538 22.8763 136.538 24.3463C136.538 25.4263 135.518 26.1163 133.718 26.1163C131.888 26.1163 130.628 25.3363 130.358 23.5663H126.578C126.818 26.8363 129.308 28.9963 133.778 28.9963Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M155.749 28.5463V13.1563H151.669V22.0363C151.669 24.0763 150.499 25.5163 148.579 25.5163C146.839 25.5163 146.029 24.5263 146.029 22.7263V13.1563H141.979V23.4163C141.979 26.7763 143.899 28.9663 147.319 28.9663C149.479 28.9663 150.679 28.1563 151.729 26.7463H151.819V28.5463H155.749Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M158.388 28.5463H162.468V19.6063C162.468 17.5663 163.578 16.2463 165.228 16.2463C166.728 16.2463 167.598 17.1463 167.598 18.8863V28.5463H171.678V19.6063C171.678 17.5663 172.728 16.2463 174.438 16.2463C175.938 16.2463 176.808 17.1463 176.808 18.8863V28.5463H180.888V18.1963C180.888 14.8363 179.058 12.7363 175.818 12.7363C173.868 12.7363 172.248 13.7563 171.198 15.4363H171.138C170.388 13.8163 168.828 12.7363 166.878 12.7363C164.748 12.7363 163.248 13.8163 162.408 15.2263H162.318V13.1563H158.388V28.5463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M0.684082 28.5463H4.76408V7.09629H0.684082V28.5463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M14.7403 28.9963C19.5103 28.9963 22.7803 25.4563 22.7803 20.8663C22.7803 16.2763 19.5103 12.7363 14.7403 12.7363C9.97025 12.7363 6.70025 16.2763 6.70025 20.8663C6.70025 25.4563 9.97025 28.9963 14.7403 28.9963ZM14.7403 25.8763C12.2203 25.8763 10.8403 23.8663 10.8403 20.8663C10.8403 17.8663 12.2203 15.8263 14.7403 15.8263C17.2303 15.8263 18.6403 17.8663 18.6403 20.8663C18.6403 23.8663 17.2303 25.8763 14.7403 25.8763Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M31.4568 33.7963C33.7368 33.7963 35.7168 33.2563 37.0068 32.0563C38.1468 31.0063 38.8368 29.5363 38.8368 27.3763V13.1563H34.9068V14.7763H34.8468C33.9168 13.4863 32.5068 12.7363 30.5868 12.7363C26.6868 12.7363 23.9268 15.6763 23.9268 20.2663C23.9268 24.9163 27.2868 27.6163 30.7068 27.6163C32.6568 27.6163 33.8268 26.8363 34.7268 25.8163H34.8168V27.4963C34.8168 29.5963 33.7068 30.7063 31.3968 30.7063C29.5068 30.7063 28.6368 29.9563 28.3068 28.9963H24.2568C24.6768 31.9963 27.2568 33.7963 31.4568 33.7963ZM31.3968 24.3463C29.2968 24.3463 27.9168 22.8163 27.9168 20.2063C27.9168 17.6263 29.2968 16.0063 31.3668 16.0063C33.8268 16.0063 35.0268 17.9263 35.0268 20.1763C35.0268 22.4563 33.9768 24.3463 31.3968 24.3463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.7539 28.9963C53.5239 28.9963 56.7939 25.4563 56.7939 20.8663C56.7939 16.2763 53.5239 12.7363 48.7539 12.7363C43.9839 12.7363 40.7139 16.2763 40.7139 20.8663C40.7139 25.4563 43.9839 28.9963 48.7539 28.9963ZM48.7539 25.8763C46.2339 25.8763 44.8539 23.8663 44.8539 20.8663C44.8539 17.8663 46.2339 15.8263 48.7539 15.8263C51.2439 15.8263 52.6539 17.8663 52.6539 20.8663C52.6539 23.8663 51.2439 25.8763 48.7539 25.8763Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M180.704 9.79629C180.704 9.10593 181.263 8.54629 181.954 8.54629H184.454C185.144 8.54629 185.704 9.10593 185.704 9.79629C185.704 10.4866 185.144 11.0463 184.454 11.0463H181.954C181.263 11.0463 180.704 10.4866 180.704 9.79629Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-75' width='186' height='41' viewBox='0 0 186 41' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M59.0372 2.72868C59.0372 1.33929 60.1758 0.212959 61.5805 0.212959H66.0111C67.0108 0.212959 67.9797 0.555658 68.7527 1.18272L70.1005 2.276L70.1342 2.30641C70.1653 2.29603 70.1964 2.28589 70.2276 2.276C72.6592 1.50561 75.6094 1.3591 78.6205 1.3591C81.6316 1.3591 84.5818 1.50561 87.0134 2.276C87.0446 2.28589 87.0757 2.29603 87.1068 2.30641L87.1405 2.276L88.4883 1.18272C89.2613 0.555658 90.2302 0.212959 91.2299 0.212959H95.6605C97.0652 0.212959 98.2038 1.33929 98.2038 2.72868V4.28386C98.2038 5.48711 97.6914 6.6347 96.7922 7.4451L95.7049 8.42509C95.1741 8.90351 94.537 9.25169 93.845 9.44151L93.5878 9.51207C94.5953 11.89 95.1519 14.4318 95.1519 16.488C95.1519 24.7594 89.978 28.3317 85.4192 31.4793C81.8291 33.9581 78.6205 36.1734 78.6205 40.213C78.6205 36.1734 75.4119 33.9581 71.8218 31.4793C67.263 28.3317 62.0891 24.7594 62.0891 16.488C62.0891 14.4318 62.6457 11.89 63.6532 9.51207L63.396 9.44151C62.704 9.25169 62.0669 8.90351 61.5361 8.42509L60.4488 7.4451C59.5496 6.6347 59.0372 5.48711 59.0372 4.28386V2.72868ZM81.9268 23.2502C81.9268 23.6454 81.7526 24.0243 81.4426 24.3038C81.1326 24.5832 80.7121 24.7402 80.2736 24.7402C79.8951 24.7402 79.5299 24.6231 79.2377 24.4113C79.7351 25.7283 81.008 26.9762 82.9441 24.9694C84.6533 23.1047 82.8681 19.1718 81.1289 16.838C80.5492 16.0601 79.5975 15.6857 78.6205 15.6857C77.6435 15.6857 76.6918 16.0601 76.1121 16.838C74.3729 19.1718 72.5877 23.1047 74.2969 24.9694C76.233 26.9762 77.5059 25.7283 78.0033 24.4113C77.7111 24.6231 77.3459 24.7402 76.9674 24.7402C76.5289 24.7402 76.1084 24.5832 75.7984 24.3038C75.4884 24.0243 75.3142 23.6454 75.3142 23.2502H81.9268ZM72.2898 11.6081H67.6844L71.3139 14.4828C72.1126 15.1153 73.28 14.9131 73.7742 14.0566C74.3982 12.9752 73.5694 11.6081 72.2898 11.6081ZM84.9512 11.6081H89.5566L85.9271 14.4828C85.1284 15.1153 83.961 14.9131 83.4668 14.0566C82.8428 12.9752 83.6716 11.6081 84.9512 11.6081Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M103.69 28.5463H107.77V13.1563H103.69V28.5463ZM103.69 10.7563H107.77V7.09629H103.69V10.7563Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M110.399 33.5863H114.479V26.8063H114.539C115.409 28.1263 116.819 28.9963 118.979 28.9963C122.939 28.9963 125.639 25.8463 125.639 20.8663C125.639 16.0663 123.029 12.7363 118.949 12.7363C116.849 12.7363 115.409 13.7263 114.419 15.0763H114.329V13.1563H110.399V33.5863ZM118.109 25.6063C115.679 25.6063 114.389 23.7763 114.389 20.9863C114.389 18.2263 115.409 16.0363 117.959 16.0363C120.479 16.0363 121.499 18.0763 121.499 20.9863C121.499 23.8963 120.179 25.6063 118.109 25.6063Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M133.778 28.9963C137.618 28.9963 140.258 27.1363 140.258 24.0463C140.258 20.4463 137.408 19.7263 134.828 19.1863C132.638 18.7363 130.598 18.6163 130.598 17.2963C130.598 16.1863 131.648 15.5863 133.238 15.5863C134.978 15.5863 136.028 16.1863 136.208 17.8363H139.898C139.598 14.7463 137.348 12.7363 133.298 12.7363C129.788 12.7363 127.028 14.3263 127.028 17.6563C127.028 21.0163 129.728 21.7663 132.488 22.3063C134.588 22.7263 136.538 22.8763 136.538 24.3463C136.538 25.4263 135.518 26.1163 133.718 26.1163C131.888 26.1163 130.628 25.3363 130.358 23.5663H126.578C126.818 26.8363 129.308 28.9963 133.778 28.9963Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M155.749 28.5463V13.1563H151.669V22.0363C151.669 24.0763 150.499 25.5163 148.579 25.5163C146.839 25.5163 146.029 24.5263 146.029 22.7263V13.1563H141.979V23.4163C141.979 26.7763 143.899 28.9663 147.319 28.9663C149.479 28.9663 150.679 28.1563 151.729 26.7463H151.819V28.5463H155.749Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M158.388 28.5463H162.468V19.6063C162.468 17.5663 163.578 16.2463 165.228 16.2463C166.728 16.2463 167.598 17.1463 167.598 18.8863V28.5463H171.678V19.6063C171.678 17.5663 172.728 16.2463 174.438 16.2463C175.938 16.2463 176.808 17.1463 176.808 18.8863V28.5463H180.888V18.1963C180.888 14.8363 179.058 12.7363 175.818 12.7363C173.868 12.7363 172.248 13.7563 171.198 15.4363H171.138C170.388 13.8163 168.828 12.7363 166.878 12.7363C164.748 12.7363 163.248 13.8163 162.408 15.2263H162.318V13.1563H158.388V28.5463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M0.684082 28.5463H4.76408V7.09629H0.684082V28.5463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M14.7403 28.9963C19.5103 28.9963 22.7803 25.4563 22.7803 20.8663C22.7803 16.2763 19.5103 12.7363 14.7403 12.7363C9.97025 12.7363 6.70025 16.2763 6.70025 20.8663C6.70025 25.4563 9.97025 28.9963 14.7403 28.9963ZM14.7403 25.8763C12.2203 25.8763 10.8403 23.8663 10.8403 20.8663C10.8403 17.8663 12.2203 15.8263 14.7403 15.8263C17.2303 15.8263 18.6403 17.8663 18.6403 20.8663C18.6403 23.8663 17.2303 25.8763 14.7403 25.8763Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M31.4568 33.7963C33.7368 33.7963 35.7168 33.2563 37.0068 32.0563C38.1468 31.0063 38.8368 29.5363 38.8368 27.3763V13.1563H34.9068V14.7763H34.8468C33.9168 13.4863 32.5068 12.7363 30.5868 12.7363C26.6868 12.7363 23.9268 15.6763 23.9268 20.2663C23.9268 24.9163 27.2868 27.6163 30.7068 27.6163C32.6568 27.6163 33.8268 26.8363 34.7268 25.8163H34.8168V27.4963C34.8168 29.5963 33.7068 30.7063 31.3968 30.7063C29.5068 30.7063 28.6368 29.9563 28.3068 28.9963H24.2568C24.6768 31.9963 27.2568 33.7963 31.4568 33.7963ZM31.3968 24.3463C29.2968 24.3463 27.9168 22.8163 27.9168 20.2063C27.9168 17.6263 29.2968 16.0063 31.3668 16.0063C33.8268 16.0063 35.0268 17.9263 35.0268 20.1763C35.0268 22.4563 33.9768 24.3463 31.3968 24.3463Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M48.7539 28.9963C53.5239 28.9963 56.7939 25.4563 56.7939 20.8663C56.7939 16.2763 53.5239 12.7363 48.7539 12.7363C43.9839 12.7363 40.7139 16.2763 40.7139 20.8663C40.7139 25.4563 43.9839 28.9963 48.7539 28.9963ZM48.7539 25.8763C46.2339 25.8763 44.8539 23.8663 44.8539 20.8663C44.8539 17.8663 46.2339 15.8263 48.7539 15.8263C51.2439 15.8263 52.6539 17.8663 52.6539 20.8663C52.6539 23.8663 51.2439 25.8763 48.7539 25.8763Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M180.704 9.79629C180.704 9.10593 181.263 8.54629 181.954 8.54629H184.454C185.144 8.54629 185.704 9.10593 185.704 9.79629C185.704 10.4866 185.144 11.0463 184.454 11.0463H181.954C181.263 11.0463 180.704 10.4866 180.704 9.79629Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-74' width='70' height='44' viewBox='0 0 70 44' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M65.5268 5.40852C65.5268 5.45982 65.5268 5.52395 65.5137 5.56243C65.4481 6.06264 65.4481 6.56285 65.4874 7.07589C65.5137 7.20415 65.5399 7.33241 65.6449 7.43502C65.8154 7.6274 66.0777 7.58893 66.1827 7.35806C66.2352 7.24263 66.2352 7.12719 66.2089 7.01176C66.0777 6.52437 66.0515 6.01134 66.0384 5.51112C66.0384 5.48547 66.0384 5.44699 66.0384 5.40852C66.1827 5.39569 66.3139 5.38286 66.4319 5.38286C66.5238 5.37004 66.6025 5.35721 66.6681 5.31873C66.8648 5.21613 66.8648 4.99809 66.6549 4.89548C66.5762 4.857 66.4713 4.84417 66.3795 4.84417C66.0515 4.857 65.7236 4.857 65.3956 4.857C65.2776 4.857 65.1595 4.86983 65.0414 4.88265C64.9758 4.89548 64.8971 4.89548 64.8447 4.93396C64.7528 4.97243 64.7004 5.03656 64.7004 5.12634C64.7135 5.21613 64.7528 5.26743 64.8447 5.30591C64.8971 5.34439 64.9627 5.35721 65.0283 5.35721C65.1857 5.37004 65.3563 5.39569 65.5268 5.40852ZM69.1342 5.99851C69.1342 6.01134 69.1473 6.02416 69.1473 6.02416C69.1998 6.37046 69.2523 6.70394 69.2916 7.03741C69.3048 7.15284 69.3179 7.25545 69.3966 7.34523C69.5671 7.56327 69.8295 7.53762 69.9475 7.30676C70 7.19132 70.0131 7.07589 69.9869 6.94763C69.9082 6.56285 69.8688 6.17807 69.7901 5.80612C69.7376 5.57525 69.6721 5.35721 69.6065 5.152C69.5671 5.02374 69.4753 4.93395 69.3179 4.92113C69.1605 4.89548 69.0424 4.97243 68.9768 5.08787C68.8981 5.19047 68.8325 5.29308 68.78 5.40852C68.6882 5.61373 68.6095 5.81895 68.5046 6.01134C68.4914 6.06264 68.4783 6.10112 68.4521 6.13959C68.439 6.11394 68.4259 6.10112 68.4259 6.10112C68.2553 5.78047 68.0979 5.45982 67.9274 5.152C67.9011 5.12634 67.888 5.10069 67.8749 5.07504C67.7962 4.95961 67.7044 4.89548 67.5601 4.89548C67.4289 4.9083 67.3239 4.98526 67.2584 5.10069C67.2321 5.152 67.2321 5.19047 67.219 5.24178C67.1665 5.65221 67.1009 6.06264 67.0485 6.47307C67.0222 6.70394 67.0091 6.9348 67.0091 7.16567C66.996 7.21697 67.0091 7.2811 67.0353 7.33241C67.0616 7.43501 67.1403 7.49915 67.2452 7.51197C67.3764 7.5248 67.4682 7.48632 67.5076 7.38371C67.5469 7.30676 67.5601 7.24263 67.5732 7.1785C67.6257 6.94763 67.665 6.72959 67.7044 6.51155C67.7306 6.38329 67.7437 6.28068 67.7831 6.13959C67.8093 6.1909 67.8355 6.22938 67.8618 6.26785C67.9798 6.42177 68.0979 6.57568 68.2422 6.70394C68.3865 6.80654 68.5046 6.79372 68.6226 6.67828C68.6489 6.65263 68.662 6.63981 68.6882 6.61415C68.8063 6.43459 68.9506 6.25503 69.0686 6.07546C69.0949 6.04981 69.108 6.02416 69.1342 5.99851Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M38.9087 5.6605C38.8175 5.90425 38.8001 6.07986 38.8422 6.22582C38.8887 6.4243 39.0094 6.48928 39.1732 6.4388C40.714 6.06627 44.0927 7.12367 45.3436 7.41838C45.6386 7.48026 45.8786 7.10791 45.6773 6.77407C45.3835 6.45077 42.0063 5.0666 40.7177 4.99113C40.2126 4.96322 39.3096 4.83658 38.9087 5.6605Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.1133 1.17982C52.2775 1.27249 52.3693 1.36089 52.4146 1.45966C52.4821 1.58922 52.4465 1.67886 52.3331 1.7246C51.3146 2.21062 49.9593 4.30303 49.4122 5.02468C49.2796 5.19069 48.9737 5.09422 48.9275 4.82122C48.937 4.51254 50.1384 2.24181 50.8089 1.62334C51.0724 1.38187 51.5077 0.908078 52.1133 1.17982Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M44.0023 0.149796C44.1996 0.00441887 44.4046 -0.0465256 44.5093 0.0479512C46.046 1.3329 46.8609 3.36773 47.3655 5.23057C47.3845 5.27397 47.3857 5.33625 47.3705 5.40122C47.3642 5.45675 47.3227 5.51541 47.2568 5.5608C47.1864 5.61091 47.1258 5.62617 47.0973 5.58299C46.4238 4.68732 42.5771 1.20242 44.0023 0.149796Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M11.461 22.4276C11.8293 22.1595 12.2297 21.9363 12.6534 21.7631C13.0967 21.6392 13.5692 21.6597 13.9995 21.8217C14.4297 21.9837 14.7944 22.2782 15.0382 22.6608C15.2563 23.0424 15.3416 23.483 15.2814 23.9162C15.2212 24.3493 15.0187 24.7516 14.7043 25.0625C14.4606 25.3145 14.1839 25.534 13.8816 25.7154C12.5342 26.5665 11.1748 27.3709 9.81547 28.222C9.53732 28.435 9.24225 28.6261 8.93308 28.7933C8.46281 29.0226 7.92537 29.084 7.41368 28.9669C6.902 28.8499 6.44826 28.5616 6.13092 28.1521C5.89369 27.8621 5.69348 27.545 5.53471 27.2077C4.24691 24.5612 2.91142 21.9263 1.67131 19.2331C1.09895 18.0673 0.633913 16.7265 0.180798 15.4324C-0.0152406 15.0564 -0.0535225 14.6205 0.0741037 14.2173C0.20173 13.8141 0.485195 13.4755 0.864201 13.2735C1.24321 13.0715 1.68785 13.0221 2.10357 13.1357C2.51929 13.2493 2.87329 13.517 3.09027 13.8818C3.75722 14.7484 4.34761 15.6689 4.85504 16.6333C6.14284 18.965 7.37103 21.2967 8.61113 23.5585C8.68334 23.6835 8.76296 23.8041 8.84961 23.9199C9.783 23.5362 10.6609 23.0345 11.461 22.4276Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M24.7761 21.6142C21.8309 24.9835 16.8943 24.1324 14.4141 19.7954C12.6493 16.7175 12.3393 11.6343 16.1789 8.42817C16.9988 7.75694 17.9792 7.29969 19.0287 7.09907C20.3155 6.9187 21.6277 7.14066 22.7777 7.73324C23.9277 8.32582 24.8567 9.25867 25.432 10.3985C27.5306 14.1293 27.2325 18.886 24.7761 21.6142ZM23.5837 13.7562C23.2708 12.8394 22.6431 12.0567 21.807 11.541C21.3339 11.2113 20.759 11.051 20.1792 11.0871C19.5993 11.1232 19.0499 11.3535 18.6233 11.7392C16.9182 13.2199 16.5604 16.7292 17.8005 18.8161C17.9586 19.1564 18.1907 19.4588 18.4808 19.7022C18.7709 19.9456 19.1119 20.1241 19.4799 20.2251C19.8479 20.3262 20.234 20.3474 20.6113 20.2873C20.9886 20.2271 21.3478 20.0871 21.664 19.877C22.5883 19.1763 23.2664 18.2115 23.604 17.1167C23.9417 16.0218 23.9221 14.8513 23.548 13.7679L23.5837 13.7562Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M36.7955 15.2252C36.494 15.2886 36.1825 15.2924 35.8794 15.2363C35.5764 15.1802 35.2878 15.0655 35.0308 14.8988C34.8059 14.773 34.6123 14.6001 34.4639 14.3924C34.3156 14.1847 34.2162 13.9475 34.1729 13.6977C34.1295 13.448 34.1434 13.192 34.2133 12.9481C34.2833 12.7042 34.4078 12.4785 34.5777 12.2872C34.8737 11.9028 35.2939 11.6276 35.7701 11.5061C37.0134 11.1533 38.2933 10.9382 39.5858 10.8649C39.8698 10.8326 40.1575 10.8561 40.432 10.934C40.7066 11.012 40.9624 11.1427 41.1846 11.3187C41.4067 11.4946 41.5907 11.7122 41.7257 11.9586C41.8606 12.205 41.9439 12.4753 41.9706 12.7536C42.3432 14.1206 42.384 15.5539 42.0898 16.9391C41.0167 21.416 37.3202 22.9549 33.1706 21.5209C32.0058 21.1375 30.9845 20.4231 30.2373 19.469C29.2407 18.32 28.5341 16.9583 28.1744 15.4934C27.883 14.1889 27.9149 12.8353 28.2676 11.5454C28.6202 10.2555 29.2833 9.06675 30.2015 8.07845C31.0729 7.00428 32.2039 6.15891 33.4926 5.61846C34.3069 5.17961 35.2598 5.05483 36.1636 5.2687C36.3686 5.32418 36.5547 5.43228 36.7026 5.58179C36.8505 5.73131 36.9548 5.91678 37.0047 6.11899C37.0546 6.32119 37.0482 6.53276 36.9863 6.73176C36.9243 6.93075 36.8091 7.10992 36.6525 7.25068C36.3547 7.51423 36.0312 7.74853 35.6866 7.9502C34.6265 8.61027 33.704 9.46082 32.9679 10.4568C32.4854 11.1013 32.1531 11.8414 31.9945 12.6249C31.8358 13.4084 31.8547 14.2164 32.0498 14.9921C32.3202 16.0497 32.9203 16.999 33.7668 17.7085C36.3901 20.0403 39.8004 17.7901 39.2042 14.6073C38.3338 14.8172 37.5706 15.0387 36.7955 15.2252Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.8217 21.8007C48.9464 24.1325 44.5345 21.8007 43.5686 16.9041C42.8651 13.4065 44.2006 8.50982 48.8749 6.64443C49.8694 6.25608 50.9481 6.11973 52.0109 6.24803C53.2878 6.47658 54.4592 7.09121 55.3598 8.00528C56.2604 8.91934 56.845 10.0867 57.0309 11.3429C57.8179 15.505 56.0293 19.947 52.8217 21.8007ZM54.1692 13.9544C54.168 12.9859 53.8176 12.0487 53.1795 11.3079C52.8384 10.8497 52.3453 10.5214 51.7843 10.3789C51.2232 10.2365 50.6291 10.2887 50.103 10.5268C48.0044 11.4128 46.5258 14.6306 47.0624 16.9974C47.1034 17.3688 47.2268 17.727 47.4241 18.0469C47.6214 18.3668 47.8878 18.6407 48.2047 18.8495C48.5215 19.0582 48.8812 19.1968 49.2585 19.2555C49.6359 19.3141 50.0218 19.2915 50.3892 19.1892C51.4985 18.8103 52.459 18.1022 53.1366 17.1637C53.8143 16.2252 54.1753 15.1032 54.1692 13.9544Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M60.9499 22.7801C60.8914 23.2068 60.662 23.5933 60.312 23.8546C59.962 24.1158 59.5202 24.2305 59.0838 24.1733C58.6474 24.1161 58.2521 23.8917 57.9849 23.5495C57.7176 23.2074 57.6004 22.7754 57.6589 22.3487C57.7174 21.922 57.9469 21.5355 58.2968 21.2742C58.6468 21.0129 59.0886 20.8983 59.525 20.9555C59.9614 21.0127 60.3567 21.237 60.624 21.5792C60.8912 21.9214 61.0085 22.3534 60.9499 22.7801ZM59.9125 7.05247C60.1393 6.71382 60.472 6.45593 60.861 6.31726C61.2499 6.17859 61.6743 6.16657 62.0708 6.283C62.4739 6.38161 62.83 6.61262 63.0797 6.93735C63.3293 7.26209 63.4572 7.66082 63.4421 8.06678C63.3895 8.71795 63.2899 9.36468 63.144 10.0021C62.7505 12.159 62.3689 14.3158 61.9516 16.4494C61.7608 17.3005 61.5104 18.1166 61.2361 18.9793C61.1407 19.249 60.9813 19.4927 60.7711 19.6905C60.6404 19.8393 60.4735 19.9534 60.2857 20.0223C60.0979 20.0913 59.8954 20.1128 59.6969 20.0849C59.4984 20.057 59.3102 19.9806 59.1499 19.8628C58.9896 19.7449 58.8623 19.5894 58.7798 19.4107C58.638 19.0901 58.561 18.7456 58.5532 18.3964C58.5532 16.9507 58.5532 15.4934 58.6486 14.036C58.8107 11.9562 59.1295 9.89088 59.6025 7.85692C59.6582 7.58442 59.7631 7.32383 59.9125 7.08745V7.05247Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M6.42311 32.1488C6.28232 32.4561 6.24371 32.7987 6.31251 33.1284C6.35828 33.563 6.45881 33.9905 6.61181 34.4011C6.80283 34.9039 7.01658 35.4011 7.28014 36.0139C7.34075 36.1549 7.40409 36.3021 7.47037 36.457C7.82579 37.2872 8.27175 38.3482 8.8666 39.8837C9.03497 40.3199 9.18448 40.7597 9.33504 41.2025C9.39586 41.3814 9.4569 41.5609 9.51938 41.7408C9.74334 42.3804 10.1287 42.955 10.6395 43.4104C10.8564 43.6607 11.1441 43.8431 11.4667 43.9343C11.7956 44.0273 12.1454 44.0214 12.4708 43.9174C12.7962 43.8133 13.082 43.6159 13.2911 43.3508C13.4961 43.0909 13.618 42.7777 13.6417 42.4505C13.7747 41.8131 13.7293 41.1522 13.5101 40.5377C13.1622 39.5174 12.7659 38.4956 12.3089 37.4962L12.3068 37.4918C11.555 35.9282 10.7908 34.3754 9.99044 32.822L9.98445 32.8111C9.75015 32.4064 9.44566 32.0446 9.08466 31.742C8.8503 31.4719 8.52703 31.2897 8.17003 31.2269C7.80542 31.1628 7.42938 31.2274 7.10904 31.4093C6.806 31.5785 6.56578 31.8374 6.42311 32.1488Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M17.9057 28.2986C16.7269 28.0001 15.4958 27.9566 14.2982 28.1712C13.3706 28.2605 12.4583 28.4697 11.8248 28.8841C11.5026 29.095 11.2421 29.3658 11.0972 29.71C10.9515 30.0561 10.9329 30.4519 11.0523 30.8929C11.2703 31.7007 11.5534 32.4861 11.8355 33.269L11.8812 33.3958L11.8823 33.3986C12.7317 35.673 13.5892 37.9397 14.4545 40.1986C14.5554 40.5546 14.6981 40.898 14.8797 41.2219L14.8831 41.2279C15.123 41.6303 15.4307 41.9902 15.7932 42.2925C15.9745 42.4587 16.1987 42.5737 16.4418 42.6251C16.6873 42.6769 16.9426 42.6619 17.1799 42.5815C17.4173 42.5012 17.6275 42.3587 17.7877 42.1695C17.9453 41.9834 18.0485 41.7592 18.0864 41.5206C18.2428 40.8724 18.1927 40.1929 17.9427 39.5733C17.8647 39.3648 17.8035 39.1517 17.739 38.9274C17.7175 38.8526 17.6957 38.7765 17.6727 38.699C19.6534 37.942 21.7609 36.9241 22.502 34.5561C22.7922 33.7378 22.8164 32.8517 22.5712 32.0193C22.3258 31.186 21.8223 30.4474 21.1301 29.9052C20.188 29.1462 19.0875 28.5978 17.9057 28.2986ZM14.6382 31.2031C14.6772 31.1921 14.7165 31.1819 14.7559 31.1724C16.0454 30.9742 17.3647 31.2383 18.4709 31.9159C18.9584 32.2474 19.1581 32.6157 19.1924 32.9701C19.2278 33.335 19.0921 33.7304 18.8195 34.1105C18.3044 34.8285 17.3644 35.4032 16.5153 35.5103C15.8963 34.1165 15.2677 32.6663 14.6382 31.2031Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M25.7646 25.7473C27.1684 25.1134 28.9073 25.0039 30.268 25.4496C30.6107 25.5472 30.908 25.7583 31.1091 26.0468C31.3089 26.3335 31.4011 26.679 31.3703 27.0244C31.3683 27.2486 31.312 27.4692 31.2061 27.6682C31.0983 27.8708 30.9422 28.045 30.751 28.1762C30.5598 28.3073 30.3391 28.3916 30.1076 28.4217C29.876 28.4519 29.6405 28.4271 29.4208 28.3494L29.4041 28.3435L29.3884 28.3354C29.276 28.2779 29.1566 28.2346 29.0331 28.2064L29.0253 28.2047C28.0681 27.9561 27.1652 28.368 26.8354 28.8741C26.6781 29.1154 26.6586 29.359 26.7896 29.5806C26.9299 29.8179 27.274 30.0842 27.9703 30.274C28.1618 30.3254 28.3581 30.375 28.5572 30.4254C29.1078 30.5648 29.68 30.7096 30.2333 30.9103L30.2354 30.9111C32.788 31.8607 33.7385 33.8274 33.4131 35.6772C33.0912 37.5065 31.5287 39.1713 29.179 39.564C28.324 39.7493 27.4342 39.7132 26.5977 39.4593C25.7591 39.2046 25.0032 38.7399 24.4051 38.1111L24.3895 38.0947C24.2007 37.8578 24.0737 37.5795 24.0174 37.2842C23.9656 37.0177 23.9929 36.7423 24.0959 36.4904C24.1983 36.24 24.3715 36.0233 24.595 35.8654C24.8311 35.6864 25.1157 35.579 25.4136 35.5566C25.7105 35.5343 26.0076 35.5974 26.2683 35.738C26.5287 35.861 26.7709 36.0179 26.9883 36.2045L26.9924 36.2079C27.377 36.5518 27.8423 36.6414 28.2885 36.5584C28.7412 36.4742 29.1669 36.2123 29.4407 35.8648C29.7127 35.5195 29.8219 35.1093 29.6923 34.7111C29.5619 34.31 29.1698 33.8606 28.3083 33.4849C28.0831 33.3914 27.8496 33.316 27.6067 33.2426C27.5412 33.2228 27.4746 33.2031 27.4072 33.1831C27.2276 33.1298 27.0428 33.0749 26.8616 33.0144C26.7368 32.9728 26.613 32.9334 26.4904 32.8943C26.1553 32.7876 25.8286 32.6836 25.5142 32.5441C24.8299 32.3163 24.2387 31.8789 23.8286 31.2966C23.4168 30.712 23.2096 30.0129 23.2378 29.3037C23.24 27.5754 24.3533 26.3847 25.7646 25.7473Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M43.5619 25.5632C43.2897 25.4332 42.9887 25.3715 42.6861 25.3836C42.3834 25.3958 42.0886 25.4814 41.8283 25.6329C41.5696 25.7833 41.353 25.9939 41.1978 26.246C41.0555 26.4583 40.957 26.6957 40.9079 26.945C40.8588 27.1941 40.86 27.4501 40.9113 27.6986C40.962 28.018 41.0182 28.3286 41.0737 28.6349C41.1656 29.1418 41.255 29.6373 41.314 30.1425L41.3162 30.1553C41.4505 30.9476 41.5208 31.7489 41.5271 32.5519L41.5277 32.5633C41.5736 33.4305 41.2714 34.2808 40.6859 34.9338L40.6766 34.9454C40.4861 35.1841 40.2314 35.3663 39.9409 35.4716C39.6505 35.5769 39.3359 35.6011 39.0322 35.5415C38.7285 35.4819 38.4478 35.3409 38.2214 35.1342C37.995 34.9275 37.8317 34.6625 37.7502 34.3704C37.5762 33.7547 37.4755 33.1214 37.4499 32.4832L37.7471 27.8569C37.7515 27.7965 37.7565 27.7345 37.7616 27.6719C37.7729 27.5314 37.7845 27.3883 37.7893 27.2548C37.7963 27.0584 37.7903 26.8564 37.7435 26.6652C37.6956 26.4698 37.6045 26.2839 37.4429 26.1256C37.2829 25.9689 37.0669 25.8533 36.7951 25.7746C36.3036 25.6355 35.888 25.6399 35.5417 25.7836C35.1952 25.9273 34.9578 26.1941 34.7898 26.5023C34.6231 26.8079 34.516 27.1697 34.435 27.5321C34.3749 27.801 34.3266 28.0833 34.2807 28.352C34.2648 28.4446 34.2493 28.5355 34.2336 28.6238L34.2332 28.6264C33.9876 30.1 33.9145 31.5962 34.0153 33.086C34.0341 33.8911 34.2058 34.6858 34.5218 35.4295C34.8783 36.3891 35.524 37.2205 36.3737 37.814C37.2252 38.4087 38.2413 38.7364 39.2875 38.7537C40.3337 38.771 41.3606 38.4771 42.2322 37.911C43.1024 37.3457 43.7768 36.5355 44.1662 35.5876C44.7109 34.3801 44.9667 33.0669 44.9139 31.7481C44.8819 30.7853 44.8283 29.8151 44.775 28.8498C44.7488 28.3763 44.7227 27.9038 44.6993 27.4342C44.6875 26.9633 44.5287 26.5072 44.2441 26.1271C44.068 25.8868 43.8336 25.693 43.5619 25.5632Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M53.1961 32.8173C53.1685 32.8516 53.1394 32.8871 53.109 32.924C52.8876 31.6752 52.6824 30.4268 52.4769 29.1765C52.4032 28.7279 52.3291 28.2774 52.2546 27.8282L52.2462 27.7781L52.219 27.7348C52.1677 27.6533 52.1626 27.5734 52.1626 27.403V27.3833L52.1595 27.3638C52.1039 27.0119 51.9411 26.6844 51.6924 26.4242C51.4444 26.1647 51.1223 25.9841 50.768 25.9057C50.4143 25.8204 50.0426 25.8392 49.6997 25.9598C49.3577 26.0801 49.0596 26.2963 48.8426 26.5813C48.6622 26.8 48.5143 27.0426 48.4035 27.3018C48.152 27.8602 47.8983 28.42 47.6439 28.9813L47.6395 28.991C47.0044 30.3923 46.365 31.803 45.7442 33.2248L45.7423 33.2294C45.3612 34.1513 45.0466 35.1227 44.7331 36.0911C44.6705 36.2844 44.6079 36.4776 44.5448 36.6703C44.4316 36.9759 44.3821 37.3005 44.3991 37.625C44.3785 37.9155 44.4496 38.2053 44.603 38.4552C44.7594 38.7102 44.9937 38.9108 45.2728 39.0289C45.5686 39.1557 45.8993 39.1826 46.2126 39.1054C46.5252 39.0283 46.8028 38.8519 47.0017 38.6039C47.2557 38.2984 47.4742 37.9652 47.6524 37.6122C48.1783 36.5604 48.6809 35.4958 49.1812 34.4358C49.3748 34.0258 49.5629 33.6586 49.7769 33.2587C49.7916 33.308 49.8066 33.3561 49.8221 33.4043C50.0464 34.3698 50.425 35.2946 50.9439 36.1448C51.0421 36.3249 51.1789 36.4823 51.3449 36.6062C51.5129 36.7316 51.7068 36.8196 51.9131 36.8643C52.1194 36.909 52.3332 36.9092 52.5396 36.8649C52.7457 36.8207 52.9402 36.7326 53.1083 36.6078L53.441 36.3643L56.0233 34.2376L55.8706 35.1891C55.661 36.497 55.453 37.794 55.232 39.0913C55.0874 39.6663 55.0876 40.2669 55.2326 40.8417C55.2954 41.1652 55.4554 41.463 55.6922 41.6972C55.931 41.9333 56.2368 42.0937 56.57 42.1577C56.9032 42.2216 57.2484 42.1862 57.5607 42.0559C57.8685 41.9276 58.1303 41.713 58.3133 41.4395C58.7391 40.923 59.0041 40.2977 59.0769 39.638C59.1865 38.7064 59.3103 37.7621 59.4342 36.8181C59.5769 35.73 59.7196 34.6422 59.8401 33.5753L59.8405 33.572C59.9565 32.4041 60.0126 31.2314 60.0087 30.058C60.0341 29.6872 59.9397 29.3178 59.7385 29.0021C59.5366 28.6853 59.2376 28.439 58.8842 28.2981C58.5166 28.1347 58.1051 28.091 57.7102 28.1736C57.3179 28.2556 56.9628 28.4578 56.6964 28.7507C56.2201 29.1814 55.7733 29.6423 55.3588 30.1304L55.356 30.1337C54.9035 30.685 54.4541 31.2471 54.0076 31.8056C53.7361 32.1451 53.4654 32.4838 53.1961 32.8173Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-74' width='70' height='44' viewBox='0 0 70 44' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M65.5268 5.40852C65.5268 5.45982 65.5268 5.52395 65.5137 5.56243C65.4481 6.06264 65.4481 6.56285 65.4874 7.07589C65.5137 7.20415 65.5399 7.33241 65.6449 7.43502C65.8154 7.6274 66.0777 7.58893 66.1827 7.35806C66.2352 7.24263 66.2352 7.12719 66.2089 7.01176C66.0777 6.52437 66.0515 6.01134 66.0384 5.51112C66.0384 5.48547 66.0384 5.44699 66.0384 5.40852C66.1827 5.39569 66.3139 5.38286 66.4319 5.38286C66.5238 5.37004 66.6025 5.35721 66.6681 5.31873C66.8648 5.21613 66.8648 4.99809 66.6549 4.89548C66.5762 4.857 66.4713 4.84417 66.3795 4.84417C66.0515 4.857 65.7236 4.857 65.3956 4.857C65.2776 4.857 65.1595 4.86983 65.0414 4.88265C64.9758 4.89548 64.8971 4.89548 64.8447 4.93396C64.7528 4.97243 64.7004 5.03656 64.7004 5.12634C64.7135 5.21613 64.7528 5.26743 64.8447 5.30591C64.8971 5.34439 64.9627 5.35721 65.0283 5.35721C65.1857 5.37004 65.3563 5.39569 65.5268 5.40852ZM69.1342 5.99851C69.1342 6.01134 69.1473 6.02416 69.1473 6.02416C69.1998 6.37046 69.2523 6.70394 69.2916 7.03741C69.3048 7.15284 69.3179 7.25545 69.3966 7.34523C69.5671 7.56327 69.8295 7.53762 69.9475 7.30676C70 7.19132 70.0131 7.07589 69.9869 6.94763C69.9082 6.56285 69.8688 6.17807 69.7901 5.80612C69.7376 5.57525 69.6721 5.35721 69.6065 5.152C69.5671 5.02374 69.4753 4.93395 69.3179 4.92113C69.1605 4.89548 69.0424 4.97243 68.9768 5.08787C68.8981 5.19047 68.8325 5.29308 68.78 5.40852C68.6882 5.61373 68.6095 5.81895 68.5046 6.01134C68.4914 6.06264 68.4783 6.10112 68.4521 6.13959C68.439 6.11394 68.4259 6.10112 68.4259 6.10112C68.2553 5.78047 68.0979 5.45982 67.9274 5.152C67.9011 5.12634 67.888 5.10069 67.8749 5.07504C67.7962 4.95961 67.7044 4.89548 67.5601 4.89548C67.4289 4.9083 67.3239 4.98526 67.2584 5.10069C67.2321 5.152 67.2321 5.19047 67.219 5.24178C67.1665 5.65221 67.1009 6.06264 67.0485 6.47307C67.0222 6.70394 67.0091 6.9348 67.0091 7.16567C66.996 7.21697 67.0091 7.2811 67.0353 7.33241C67.0616 7.43501 67.1403 7.49915 67.2452 7.51197C67.3764 7.5248 67.4682 7.48632 67.5076 7.38371C67.5469 7.30676 67.5601 7.24263 67.5732 7.1785C67.6257 6.94763 67.665 6.72959 67.7044 6.51155C67.7306 6.38329 67.7437 6.28068 67.7831 6.13959C67.8093 6.1909 67.8355 6.22938 67.8618 6.26785C67.9798 6.42177 68.0979 6.57568 68.2422 6.70394C68.3865 6.80654 68.5046 6.79372 68.6226 6.67828C68.6489 6.65263 68.662 6.63981 68.6882 6.61415C68.8063 6.43459 68.9506 6.25503 69.0686 6.07546C69.0949 6.04981 69.108 6.02416 69.1342 5.99851Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M38.9087 5.6605C38.8175 5.90425 38.8001 6.07986 38.8422 6.22582C38.8887 6.4243 39.0094 6.48928 39.1732 6.4388C40.714 6.06627 44.0927 7.12367 45.3436 7.41838C45.6386 7.48026 45.8786 7.10791 45.6773 6.77407C45.3835 6.45077 42.0063 5.0666 40.7177 4.99113C40.2126 4.96322 39.3096 4.83658 38.9087 5.6605Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.1133 1.17982C52.2775 1.27249 52.3693 1.36089 52.4146 1.45966C52.4821 1.58922 52.4465 1.67886 52.3331 1.7246C51.3146 2.21062 49.9593 4.30303 49.4122 5.02468C49.2796 5.19069 48.9737 5.09422 48.9275 4.82122C48.937 4.51254 50.1384 2.24181 50.8089 1.62334C51.0724 1.38187 51.5077 0.908078 52.1133 1.17982Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M44.0023 0.149796C44.1996 0.00441887 44.4046 -0.0465256 44.5093 0.0479512C46.046 1.3329 46.8609 3.36773 47.3655 5.23057C47.3845 5.27397 47.3857 5.33625 47.3705 5.40122C47.3642 5.45675 47.3227 5.51541 47.2568 5.5608C47.1864 5.61091 47.1258 5.62617 47.0973 5.58299C46.4238 4.68732 42.5771 1.20242 44.0023 0.149796Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M11.461 22.4276C11.8293 22.1595 12.2297 21.9363 12.6534 21.7631C13.0967 21.6392 13.5692 21.6597 13.9995 21.8217C14.4297 21.9837 14.7944 22.2782 15.0382 22.6608C15.2563 23.0424 15.3416 23.483 15.2814 23.9162C15.2212 24.3493 15.0187 24.7516 14.7043 25.0625C14.4606 25.3145 14.1839 25.534 13.8816 25.7154C12.5342 26.5665 11.1748 27.3709 9.81547 28.222C9.53732 28.435 9.24225 28.6261 8.93308 28.7933C8.46281 29.0226 7.92537 29.084 7.41368 28.9669C6.902 28.8499 6.44826 28.5616 6.13092 28.1521C5.89369 27.8621 5.69348 27.545 5.53471 27.2077C4.24691 24.5612 2.91142 21.9263 1.67131 19.2331C1.09895 18.0673 0.633913 16.7265 0.180798 15.4324C-0.0152406 15.0564 -0.0535225 14.6205 0.0741037 14.2173C0.20173 13.8141 0.485195 13.4755 0.864201 13.2735C1.24321 13.0715 1.68785 13.0221 2.10357 13.1357C2.51929 13.2493 2.87329 13.517 3.09027 13.8818C3.75722 14.7484 4.34761 15.6689 4.85504 16.6333C6.14284 18.965 7.37103 21.2967 8.61113 23.5585C8.68334 23.6835 8.76296 23.8041 8.84961 23.9199C9.783 23.5362 10.6609 23.0345 11.461 22.4276Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M24.7761 21.6142C21.8309 24.9835 16.8943 24.1324 14.4141 19.7954C12.6493 16.7175 12.3393 11.6343 16.1789 8.42817C16.9988 7.75694 17.9792 7.29969 19.0287 7.09907C20.3155 6.9187 21.6277 7.14066 22.7777 7.73324C23.9277 8.32582 24.8567 9.25867 25.432 10.3985C27.5306 14.1293 27.2325 18.886 24.7761 21.6142ZM23.5837 13.7562C23.2708 12.8394 22.6431 12.0567 21.807 11.541C21.3339 11.2113 20.759 11.051 20.1792 11.0871C19.5993 11.1232 19.0499 11.3535 18.6233 11.7392C16.9182 13.2199 16.5604 16.7292 17.8005 18.8161C17.9586 19.1564 18.1907 19.4588 18.4808 19.7022C18.7709 19.9456 19.1119 20.1241 19.4799 20.2251C19.8479 20.3262 20.234 20.3474 20.6113 20.2873C20.9886 20.2271 21.3478 20.0871 21.664 19.877C22.5883 19.1763 23.2664 18.2115 23.604 17.1167C23.9417 16.0218 23.9221 14.8513 23.548 13.7679L23.5837 13.7562Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M36.7955 15.2252C36.494 15.2886 36.1825 15.2924 35.8794 15.2363C35.5764 15.1802 35.2878 15.0655 35.0308 14.8988C34.8059 14.773 34.6123 14.6001 34.4639 14.3924C34.3156 14.1847 34.2162 13.9475 34.1729 13.6977C34.1295 13.448 34.1434 13.192 34.2133 12.9481C34.2833 12.7042 34.4078 12.4785 34.5777 12.2872C34.8737 11.9028 35.2939 11.6276 35.7701 11.5061C37.0134 11.1533 38.2933 10.9382 39.5858 10.8649C39.8698 10.8326 40.1575 10.8561 40.432 10.934C40.7066 11.012 40.9624 11.1427 41.1846 11.3187C41.4067 11.4946 41.5907 11.7122 41.7257 11.9586C41.8606 12.205 41.9439 12.4753 41.9706 12.7536C42.3432 14.1206 42.384 15.5539 42.0898 16.9391C41.0167 21.416 37.3202 22.9549 33.1706 21.5209C32.0058 21.1375 30.9845 20.4231 30.2373 19.469C29.2407 18.32 28.5341 16.9583 28.1744 15.4934C27.883 14.1889 27.9149 12.8353 28.2676 11.5454C28.6202 10.2555 29.2833 9.06675 30.2015 8.07845C31.0729 7.00428 32.2039 6.15891 33.4926 5.61846C34.3069 5.17961 35.2598 5.05483 36.1636 5.2687C36.3686 5.32418 36.5547 5.43228 36.7026 5.58179C36.8505 5.73131 36.9548 5.91678 37.0047 6.11899C37.0546 6.32119 37.0482 6.53276 36.9863 6.73176C36.9243 6.93075 36.8091 7.10992 36.6525 7.25068C36.3547 7.51423 36.0312 7.74853 35.6866 7.9502C34.6265 8.61027 33.704 9.46082 32.9679 10.4568C32.4854 11.1013 32.1531 11.8414 31.9945 12.6249C31.8358 13.4084 31.8547 14.2164 32.0498 14.9921C32.3202 16.0497 32.9203 16.999 33.7668 17.7085C36.3901 20.0403 39.8004 17.7901 39.2042 14.6073C38.3338 14.8172 37.5706 15.0387 36.7955 15.2252Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M52.8217 21.8007C48.9464 24.1325 44.5345 21.8007 43.5686 16.9041C42.8651 13.4065 44.2006 8.50982 48.8749 6.64443C49.8694 6.25608 50.9481 6.11973 52.0109 6.24803C53.2878 6.47658 54.4592 7.09121 55.3598 8.00528C56.2604 8.91934 56.845 10.0867 57.0309 11.3429C57.8179 15.505 56.0293 19.947 52.8217 21.8007ZM54.1692 13.9544C54.168 12.9859 53.8176 12.0487 53.1795 11.3079C52.8384 10.8497 52.3453 10.5214 51.7843 10.3789C51.2232 10.2365 50.6291 10.2887 50.103 10.5268C48.0044 11.4128 46.5258 14.6306 47.0624 16.9974C47.1034 17.3688 47.2268 17.727 47.4241 18.0469C47.6214 18.3668 47.8878 18.6407 48.2047 18.8495C48.5215 19.0582 48.8812 19.1968 49.2585 19.2555C49.6359 19.3141 50.0218 19.2915 50.3892 19.1892C51.4985 18.8103 52.459 18.1022 53.1366 17.1637C53.8143 16.2252 54.1753 15.1032 54.1692 13.9544Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M60.9499 22.7801C60.8914 23.2068 60.662 23.5933 60.312 23.8546C59.962 24.1158 59.5202 24.2305 59.0838 24.1733C58.6474 24.1161 58.2521 23.8917 57.9849 23.5495C57.7176 23.2074 57.6004 22.7754 57.6589 22.3487C57.7174 21.922 57.9469 21.5355 58.2968 21.2742C58.6468 21.0129 59.0886 20.8983 59.525 20.9555C59.9614 21.0127 60.3567 21.237 60.624 21.5792C60.8912 21.9214 61.0085 22.3534 60.9499 22.7801ZM59.9125 7.05247C60.1393 6.71382 60.472 6.45593 60.861 6.31726C61.2499 6.17859 61.6743 6.16657 62.0708 6.283C62.4739 6.38161 62.83 6.61262 63.0797 6.93735C63.3293 7.26209 63.4572 7.66082 63.4421 8.06678C63.3895 8.71795 63.2899 9.36468 63.144 10.0021C62.7505 12.159 62.3689 14.3158 61.9516 16.4494C61.7608 17.3005 61.5104 18.1166 61.2361 18.9793C61.1407 19.249 60.9813 19.4927 60.7711 19.6905C60.6404 19.8393 60.4735 19.9534 60.2857 20.0223C60.0979 20.0913 59.8954 20.1128 59.6969 20.0849C59.4984 20.057 59.3102 19.9806 59.1499 19.8628C58.9896 19.7449 58.8623 19.5894 58.7798 19.4107C58.638 19.0901 58.561 18.7456 58.5532 18.3964C58.5532 16.9507 58.5532 15.4934 58.6486 14.036C58.8107 11.9562 59.1295 9.89088 59.6025 7.85692C59.6582 7.58442 59.7631 7.32383 59.9125 7.08745V7.05247Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M6.42311 32.1488C6.28232 32.4561 6.24371 32.7987 6.31251 33.1284C6.35828 33.563 6.45881 33.9905 6.61181 34.4011C6.80283 34.9039 7.01658 35.4011 7.28014 36.0139C7.34075 36.1549 7.40409 36.3021 7.47037 36.457C7.82579 37.2872 8.27175 38.3482 8.8666 39.8837C9.03497 40.3199 9.18448 40.7597 9.33504 41.2025C9.39586 41.3814 9.4569 41.5609 9.51938 41.7408C9.74334 42.3804 10.1287 42.955 10.6395 43.4104C10.8564 43.6607 11.1441 43.8431 11.4667 43.9343C11.7956 44.0273 12.1454 44.0214 12.4708 43.9174C12.7962 43.8133 13.082 43.6159 13.2911 43.3508C13.4961 43.0909 13.618 42.7777 13.6417 42.4505C13.7747 41.8131 13.7293 41.1522 13.5101 40.5377C13.1622 39.5174 12.7659 38.4956 12.3089 37.4962L12.3068 37.4918C11.555 35.9282 10.7908 34.3754 9.99044 32.822L9.98445 32.8111C9.75015 32.4064 9.44566 32.0446 9.08466 31.742C8.8503 31.4719 8.52703 31.2897 8.17003 31.2269C7.80542 31.1628 7.42938 31.2274 7.10904 31.4093C6.806 31.5785 6.56578 31.8374 6.42311 32.1488Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M17.9057 28.2986C16.7269 28.0001 15.4958 27.9566 14.2982 28.1712C13.3706 28.2605 12.4583 28.4697 11.8248 28.8841C11.5026 29.095 11.2421 29.3658 11.0972 29.71C10.9515 30.0561 10.9329 30.4519 11.0523 30.8929C11.2703 31.7007 11.5534 32.4861 11.8355 33.269L11.8812 33.3958L11.8823 33.3986C12.7317 35.673 13.5892 37.9397 14.4545 40.1986C14.5554 40.5546 14.6981 40.898 14.8797 41.2219L14.8831 41.2279C15.123 41.6303 15.4307 41.9902 15.7932 42.2925C15.9745 42.4587 16.1987 42.5737 16.4418 42.6251C16.6873 42.6769 16.9426 42.6619 17.1799 42.5815C17.4173 42.5012 17.6275 42.3587 17.7877 42.1695C17.9453 41.9834 18.0485 41.7592 18.0864 41.5206C18.2428 40.8724 18.1927 40.1929 17.9427 39.5733C17.8647 39.3648 17.8035 39.1517 17.739 38.9274C17.7175 38.8526 17.6957 38.7765 17.6727 38.699C19.6534 37.942 21.7609 36.9241 22.502 34.5561C22.7922 33.7378 22.8164 32.8517 22.5712 32.0193C22.3258 31.186 21.8223 30.4474 21.1301 29.9052C20.188 29.1462 19.0875 28.5978 17.9057 28.2986ZM14.6382 31.2031C14.6772 31.1921 14.7165 31.1819 14.7559 31.1724C16.0454 30.9742 17.3647 31.2383 18.4709 31.9159C18.9584 32.2474 19.1581 32.6157 19.1924 32.9701C19.2278 33.335 19.0921 33.7304 18.8195 34.1105C18.3044 34.8285 17.3644 35.4032 16.5153 35.5103C15.8963 34.1165 15.2677 32.6663 14.6382 31.2031Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M25.7646 25.7473C27.1684 25.1134 28.9073 25.0039 30.268 25.4496C30.6107 25.5472 30.908 25.7583 31.1091 26.0468C31.3089 26.3335 31.4011 26.679 31.3703 27.0244C31.3683 27.2486 31.312 27.4692 31.2061 27.6682C31.0983 27.8708 30.9422 28.045 30.751 28.1762C30.5598 28.3073 30.3391 28.3916 30.1076 28.4217C29.876 28.4519 29.6405 28.4271 29.4208 28.3494L29.4041 28.3435L29.3884 28.3354C29.276 28.2779 29.1566 28.2346 29.0331 28.2064L29.0253 28.2047C28.0681 27.9561 27.1652 28.368 26.8354 28.8741C26.6781 29.1154 26.6586 29.359 26.7896 29.5806C26.9299 29.8179 27.274 30.0842 27.9703 30.274C28.1618 30.3254 28.3581 30.375 28.5572 30.4254C29.1078 30.5648 29.68 30.7096 30.2333 30.9103L30.2354 30.9111C32.788 31.8607 33.7385 33.8274 33.4131 35.6772C33.0912 37.5065 31.5287 39.1713 29.179 39.564C28.324 39.7493 27.4342 39.7132 26.5977 39.4593C25.7591 39.2046 25.0032 38.7399 24.4051 38.1111L24.3895 38.0947C24.2007 37.8578 24.0737 37.5795 24.0174 37.2842C23.9656 37.0177 23.9929 36.7423 24.0959 36.4904C24.1983 36.24 24.3715 36.0233 24.595 35.8654C24.8311 35.6864 25.1157 35.579 25.4136 35.5566C25.7105 35.5343 26.0076 35.5974 26.2683 35.738C26.5287 35.861 26.7709 36.0179 26.9883 36.2045L26.9924 36.2079C27.377 36.5518 27.8423 36.6414 28.2885 36.5584C28.7412 36.4742 29.1669 36.2123 29.4407 35.8648C29.7127 35.5195 29.8219 35.1093 29.6923 34.7111C29.5619 34.31 29.1698 33.8606 28.3083 33.4849C28.0831 33.3914 27.8496 33.316 27.6067 33.2426C27.5412 33.2228 27.4746 33.2031 27.4072 33.1831C27.2276 33.1298 27.0428 33.0749 26.8616 33.0144C26.7368 32.9728 26.613 32.9334 26.4904 32.8943C26.1553 32.7876 25.8286 32.6836 25.5142 32.5441C24.8299 32.3163 24.2387 31.8789 23.8286 31.2966C23.4168 30.712 23.2096 30.0129 23.2378 29.3037C23.24 27.5754 24.3533 26.3847 25.7646 25.7473Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M43.5619 25.5632C43.2897 25.4332 42.9887 25.3715 42.6861 25.3836C42.3834 25.3958 42.0886 25.4814 41.8283 25.6329C41.5696 25.7833 41.353 25.9939 41.1978 26.246C41.0555 26.4583 40.957 26.6957 40.9079 26.945C40.8588 27.1941 40.86 27.4501 40.9113 27.6986C40.962 28.018 41.0182 28.3286 41.0737 28.6349C41.1656 29.1418 41.255 29.6373 41.314 30.1425L41.3162 30.1553C41.4505 30.9476 41.5208 31.7489 41.5271 32.5519L41.5277 32.5633C41.5736 33.4305 41.2714 34.2808 40.6859 34.9338L40.6766 34.9454C40.4861 35.1841 40.2314 35.3663 39.9409 35.4716C39.6505 35.5769 39.3359 35.6011 39.0322 35.5415C38.7285 35.4819 38.4478 35.3409 38.2214 35.1342C37.995 34.9275 37.8317 34.6625 37.7502 34.3704C37.5762 33.7547 37.4755 33.1214 37.4499 32.4832L37.7471 27.8569C37.7515 27.7965 37.7565 27.7345 37.7616 27.6719C37.7729 27.5314 37.7845 27.3883 37.7893 27.2548C37.7963 27.0584 37.7903 26.8564 37.7435 26.6652C37.6956 26.4698 37.6045 26.2839 37.4429 26.1256C37.2829 25.9689 37.0669 25.8533 36.7951 25.7746C36.3036 25.6355 35.888 25.6399 35.5417 25.7836C35.1952 25.9273 34.9578 26.1941 34.7898 26.5023C34.6231 26.8079 34.516 27.1697 34.435 27.5321C34.3749 27.801 34.3266 28.0833 34.2807 28.352C34.2648 28.4446 34.2493 28.5355 34.2336 28.6238L34.2332 28.6264C33.9876 30.1 33.9145 31.5962 34.0153 33.086C34.0341 33.8911 34.2058 34.6858 34.5218 35.4295C34.8783 36.3891 35.524 37.2205 36.3737 37.814C37.2252 38.4087 38.2413 38.7364 39.2875 38.7537C40.3337 38.771 41.3606 38.4771 42.2322 37.911C43.1024 37.3457 43.7768 36.5355 44.1662 35.5876C44.7109 34.3801 44.9667 33.0669 44.9139 31.7481C44.8819 30.7853 44.8283 29.8151 44.775 28.8498C44.7488 28.3763 44.7227 27.9038 44.6993 27.4342C44.6875 26.9633 44.5287 26.5072 44.2441 26.1271C44.068 25.8868 43.8336 25.693 43.5619 25.5632Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M53.1961 32.8173C53.1685 32.8516 53.1394 32.8871 53.109 32.924C52.8876 31.6752 52.6824 30.4268 52.4769 29.1765C52.4032 28.7279 52.3291 28.2774 52.2546 27.8282L52.2462 27.7781L52.219 27.7348C52.1677 27.6533 52.1626 27.5734 52.1626 27.403V27.3833L52.1595 27.3638C52.1039 27.0119 51.9411 26.6844 51.6924 26.4242C51.4444 26.1647 51.1223 25.9841 50.768 25.9057C50.4143 25.8204 50.0426 25.8392 49.6997 25.9598C49.3577 26.0801 49.0596 26.2963 48.8426 26.5813C48.6622 26.8 48.5143 27.0426 48.4035 27.3018C48.152 27.8602 47.8983 28.42 47.6439 28.9813L47.6395 28.991C47.0044 30.3923 46.365 31.803 45.7442 33.2248L45.7423 33.2294C45.3612 34.1513 45.0466 35.1227 44.7331 36.0911C44.6705 36.2844 44.6079 36.4776 44.5448 36.6703C44.4316 36.9759 44.3821 37.3005 44.3991 37.625C44.3785 37.9155 44.4496 38.2053 44.603 38.4552C44.7594 38.7102 44.9937 38.9108 45.2728 39.0289C45.5686 39.1557 45.8993 39.1826 46.2126 39.1054C46.5252 39.0283 46.8028 38.8519 47.0017 38.6039C47.2557 38.2984 47.4742 37.9652 47.6524 37.6122C48.1783 36.5604 48.6809 35.4958 49.1812 34.4358C49.3748 34.0258 49.5629 33.6586 49.7769 33.2587C49.7916 33.308 49.8066 33.3561 49.8221 33.4043C50.0464 34.3698 50.425 35.2946 50.9439 36.1448C51.0421 36.3249 51.1789 36.4823 51.3449 36.6062C51.5129 36.7316 51.7068 36.8196 51.9131 36.8643C52.1194 36.909 52.3332 36.9092 52.5396 36.8649C52.7457 36.8207 52.9402 36.7326 53.1083 36.6078L53.441 36.3643L56.0233 34.2376L55.8706 35.1891C55.661 36.497 55.453 37.794 55.232 39.0913C55.0874 39.6663 55.0876 40.2669 55.2326 40.8417C55.2954 41.1652 55.4554 41.463 55.6922 41.6972C55.931 41.9333 56.2368 42.0937 56.57 42.1577C56.9032 42.2216 57.2484 42.1862 57.5607 42.0559C57.8685 41.9276 58.1303 41.713 58.3133 41.4395C58.7391 40.923 59.0041 40.2977 59.0769 39.638C59.1865 38.7064 59.3103 37.7621 59.4342 36.8181C59.5769 35.73 59.7196 34.6422 59.8401 33.5753L59.8405 33.572C59.9565 32.4041 60.0126 31.2314 60.0087 30.058C60.0341 29.6872 59.9397 29.3178 59.7385 29.0021C59.5366 28.6853 59.2376 28.439 58.8842 28.2981C58.5166 28.1347 58.1051 28.091 57.7102 28.1736C57.3179 28.2556 56.9628 28.4578 56.6964 28.7507C56.2201 29.1814 55.7733 29.6423 55.3588 30.1304L55.356 30.1337C54.9035 30.685 54.4541 31.2471 54.0076 31.8056C53.7361 32.1451 53.4654 32.4838 53.1961 32.8173Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					},
					{
						"image": {
							"alt": "",
							"src": "data:image/svg+xml,%3Csvg id='logo-76' width='218' height='40' viewBox='0 0 218 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M122.355 29.5238H127.018V11.9352H122.355V29.5238ZM122.355 9.19238H127.018V5.00952H122.355V9.19238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M130.023 35.2838H134.686V27.5352H134.754C135.748 29.0438 137.36 30.0381 139.828 30.0381C144.354 30.0381 147.44 26.4381 147.44 20.7467C147.44 15.2609 144.457 11.4552 139.794 11.4552C137.394 11.4552 135.748 12.5867 134.617 14.1295H134.514V11.9352H130.023V35.2838ZM138.834 26.1638C136.057 26.1638 134.583 24.0724 134.583 20.8838C134.583 17.7295 135.748 15.2267 138.663 15.2267C141.543 15.2267 142.708 17.5581 142.708 20.8838C142.708 24.2095 141.2 26.1638 138.834 26.1638Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M156.741 30.0381C161.13 30.0381 164.147 27.9124 164.147 24.3809C164.147 20.2667 160.89 19.4438 157.941 18.8267C155.438 18.3124 153.107 18.1752 153.107 16.6667C153.107 15.3981 154.307 14.7124 156.124 14.7124C158.113 14.7124 159.313 15.3981 159.518 17.2838H163.735C163.393 13.7524 160.821 11.4552 156.193 11.4552C152.181 11.4552 149.027 13.2724 149.027 17.0781C149.027 20.9181 152.113 21.7752 155.267 22.3924C157.667 22.8724 159.895 23.0438 159.895 24.7238C159.895 25.9581 158.73 26.7467 156.673 26.7467C154.581 26.7467 153.141 25.8552 152.833 23.8324H148.513C148.787 27.5695 151.633 30.0381 156.741 30.0381Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M181.85 29.5238V11.9352H177.187V22.0838C177.187 24.4152 175.85 26.0609 173.656 26.0609C171.667 26.0609 170.742 24.9295 170.742 22.8724V11.9352H166.113V23.6609C166.113 27.5009 168.307 30.0038 172.216 30.0038C174.685 30.0038 176.056 29.0781 177.256 27.4667H177.359V29.5238H181.85Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M184.866 29.5238H189.529V19.3067C189.529 16.9752 190.798 15.4667 192.684 15.4667C194.398 15.4667 195.392 16.4952 195.392 18.4838V29.5238H200.055V19.3067C200.055 16.9752 201.255 15.4667 203.209 15.4667C204.924 15.4667 205.918 16.4952 205.918 18.4838V29.5238H210.581V17.6952C210.581 13.8552 208.489 11.4552 204.786 11.4552C202.558 11.4552 200.706 12.6209 199.506 14.5409H199.438C198.581 12.6895 196.798 11.4552 194.569 11.4552C192.135 11.4552 190.421 12.6895 189.461 14.3009H189.358V11.9352H184.866V29.5238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M0.824158 29.5238H5.48701V5.00952H0.824158V29.5238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M16.8884 30.0381C22.3398 30.0381 26.0769 25.9924 26.0769 20.7467C26.0769 15.5009 22.3398 11.4552 16.8884 11.4552C11.4369 11.4552 7.69978 15.5009 7.69978 20.7467C7.69978 25.9924 11.4369 30.0381 16.8884 30.0381ZM16.8884 26.4724C14.0084 26.4724 12.4312 24.1752 12.4312 20.7467C12.4312 17.3181 14.0084 14.9867 16.8884 14.9867C19.7341 14.9867 21.3455 17.3181 21.3455 20.7467C21.3455 24.1752 19.7341 26.4724 16.8884 26.4724Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M35.993 35.5238C38.5987 35.5238 40.8616 34.9067 42.3358 33.5352C43.6387 32.3352 44.4273 30.6552 44.4273 28.1867V11.9352H39.9359V13.7867H39.8673C38.8044 12.3124 37.193 11.4552 34.9987 11.4552C30.5416 11.4552 27.3873 14.8152 27.3873 20.0609C27.3873 25.3752 31.2273 28.4609 35.1359 28.4609C37.3644 28.4609 38.7016 27.5695 39.7301 26.4038H39.833V28.3238C39.833 30.7238 38.5644 31.9924 35.9244 31.9924C33.7644 31.9924 32.7701 31.1352 32.393 30.0381H27.7644C28.2444 33.4667 31.193 35.5238 35.993 35.5238ZM35.9244 24.7238C33.5244 24.7238 31.9473 22.9752 31.9473 19.9924C31.9473 17.0438 33.5244 15.1924 35.8901 15.1924C38.7016 15.1924 40.073 17.3867 40.073 19.9581C40.073 22.5638 38.873 24.7238 35.9244 24.7238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M55.7611 30.0381C61.2125 30.0381 64.9497 25.9924 64.9497 20.7467C64.9497 15.5009 61.2125 11.4552 55.7611 11.4552C50.3097 11.4552 46.5725 15.5009 46.5725 20.7467C46.5725 25.9924 50.3097 30.0381 55.7611 30.0381ZM55.7611 26.4724C52.8811 26.4724 51.304 24.1752 51.304 20.7467C51.304 17.3181 52.8811 14.9867 55.7611 14.9867C58.6068 14.9867 60.2183 17.3181 60.2183 20.7467C60.2183 24.1752 58.6068 26.4724 55.7611 26.4724Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M212.275 9.04762C212.275 8.25864 212.915 7.61905 213.704 7.61905H216.561C217.35 7.61905 217.99 8.25864 217.99 9.04762C217.99 9.8366 217.35 10.4762 216.561 10.4762H213.704C212.915 10.4762 212.275 9.8366 212.275 9.04762Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M93.2277 0C104.273 0 113.228 8.95431 113.228 20C113.228 31.0457 104.273 40 93.2277 40C82.182 40 73.2277 31.0457 73.2277 20C73.2277 8.95431 82.182 0 93.2277 0ZM92.5048 1.49659C90.2231 1.81769 88.0505 3.65108 86.364 6.7174C85.8748 7.60683 85.4334 8.58946 85.0488 9.65044C87.342 9.07417 89.8611 8.73442 92.5048 8.68187V1.49659ZM83.3584 10.1308C83.8368 8.62958 84.4219 7.2484 85.0972 6.02065C85.9332 4.50059 86.9254 3.18795 88.0433 2.17977C81.9644 3.94523 77.1729 8.73679 75.4074 14.8157C76.4156 13.6978 77.7282 12.7056 79.2483 11.8696C80.4761 11.1943 81.8572 10.6091 83.3584 10.1308ZM82.8781 11.8211C82.3018 14.1143 81.9621 16.6334 81.9095 19.2771H74.7242C75.0453 16.9954 76.8787 14.8228 79.9451 13.1364C80.8345 12.6472 81.8171 12.2058 82.8781 11.8211ZM83.3556 19.2771C83.4153 16.392 83.8307 13.6834 84.5179 11.2902C86.9111 10.603 89.6197 10.1876 92.5048 10.1279V13.2508C91.4285 16.0062 89.2333 18.2012 86.4778 19.2771H83.3556ZM81.9095 20.7229H74.7242C75.0453 23.0046 76.8787 25.1771 79.9451 26.8636C80.8345 27.3528 81.8171 27.7942 82.8781 28.1789C82.3018 25.8857 81.9621 23.3666 81.9095 20.7229ZM84.5179 28.7098C83.8307 26.3166 83.4153 23.608 83.3556 20.7229H86.4778C89.2333 21.7988 91.4285 23.9938 92.5048 26.7492V29.8721C89.6197 29.8124 86.9111 29.397 84.5179 28.7098ZM83.3584 29.8692C81.8572 29.3909 80.4761 28.8057 79.2483 28.1304C77.7282 27.2944 76.4156 26.3022 75.4074 25.1843C77.1729 31.2632 81.9644 36.0548 88.0433 37.8202C86.9254 36.812 85.9332 35.4994 85.0972 33.9793C84.4219 32.7516 83.8368 31.3704 83.3584 29.8692ZM92.5048 38.5034C90.2231 38.1823 88.0505 36.3489 86.364 33.2826C85.8748 32.3932 85.4334 31.4105 85.0488 30.3496C87.342 30.9258 89.8611 31.2656 92.5048 31.3181V38.5034ZM98.412 37.8202C99.5299 36.812 100.522 35.4994 101.358 33.9793C102.033 32.7516 102.619 31.3704 103.097 29.8692C104.598 29.3909 105.979 28.8057 107.207 28.1304C108.727 27.2944 110.04 26.3022 111.048 25.1843C109.282 31.2632 104.491 36.0548 98.412 37.8202ZM101.407 30.3496C101.022 31.4105 100.58 32.3932 100.091 33.2826C98.4048 36.3489 96.2322 38.1823 93.9505 38.5034V31.3181C96.5942 31.2656 99.1133 30.9258 101.407 30.3496ZM103.577 28.1789C104.638 27.7942 105.621 27.3528 106.51 26.8636C109.577 25.1772 111.41 23.0046 111.731 20.7229H104.546C104.493 23.3666 104.153 25.8857 103.577 28.1789ZM103.1 20.7229C103.04 23.608 102.625 26.3166 101.937 28.7098C99.5442 29.397 96.8356 29.8124 93.9505 29.8721V26.7515C95.0265 23.9951 97.2222 21.7991 99.9784 20.7229H103.1ZM104.546 19.2771H111.731C111.41 16.9954 109.577 14.8228 106.51 13.1364C105.621 12.6472 104.638 12.2058 103.577 11.8211C104.153 14.1143 104.493 16.6334 104.546 19.2771ZM101.937 11.2902C102.625 13.6834 103.04 16.392 103.1 19.2771H99.9785C97.2222 18.2009 95.0265 16.0049 93.9505 13.2485V10.1279C96.8356 10.1876 99.5442 10.603 101.937 11.2902ZM103.097 10.1308C104.598 10.6091 105.979 11.1943 107.207 11.8696C108.727 12.7056 110.04 13.6978 111.048 14.8157C109.282 8.73679 104.491 3.94523 98.412 2.17977C99.5299 3.18795 100.522 4.50059 101.358 6.02065C102.033 7.2484 102.619 8.62958 103.097 10.1308ZM93.9505 1.49659C96.2322 1.81769 98.4048 3.65108 100.091 6.7174C100.58 7.60684 101.022 8.58946 101.407 9.65044C99.1133 9.07417 96.5942 8.73442 93.9505 8.68187V1.49659Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"url": "data:image/svg+xml,%3Csvg id='logo-76' width='218' height='40' viewBox='0 0 218 40' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cpath class='ccustom' d='M122.355 29.5238H127.018V11.9352H122.355V29.5238ZM122.355 9.19238H127.018V5.00952H122.355V9.19238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M130.023 35.2838H134.686V27.5352H134.754C135.748 29.0438 137.36 30.0381 139.828 30.0381C144.354 30.0381 147.44 26.4381 147.44 20.7467C147.44 15.2609 144.457 11.4552 139.794 11.4552C137.394 11.4552 135.748 12.5867 134.617 14.1295H134.514V11.9352H130.023V35.2838ZM138.834 26.1638C136.057 26.1638 134.583 24.0724 134.583 20.8838C134.583 17.7295 135.748 15.2267 138.663 15.2267C141.543 15.2267 142.708 17.5581 142.708 20.8838C142.708 24.2095 141.2 26.1638 138.834 26.1638Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M156.741 30.0381C161.13 30.0381 164.147 27.9124 164.147 24.3809C164.147 20.2667 160.89 19.4438 157.941 18.8267C155.438 18.3124 153.107 18.1752 153.107 16.6667C153.107 15.3981 154.307 14.7124 156.124 14.7124C158.113 14.7124 159.313 15.3981 159.518 17.2838H163.735C163.393 13.7524 160.821 11.4552 156.193 11.4552C152.181 11.4552 149.027 13.2724 149.027 17.0781C149.027 20.9181 152.113 21.7752 155.267 22.3924C157.667 22.8724 159.895 23.0438 159.895 24.7238C159.895 25.9581 158.73 26.7467 156.673 26.7467C154.581 26.7467 153.141 25.8552 152.833 23.8324H148.513C148.787 27.5695 151.633 30.0381 156.741 30.0381Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M181.85 29.5238V11.9352H177.187V22.0838C177.187 24.4152 175.85 26.0609 173.656 26.0609C171.667 26.0609 170.742 24.9295 170.742 22.8724V11.9352H166.113V23.6609C166.113 27.5009 168.307 30.0038 172.216 30.0038C174.685 30.0038 176.056 29.0781 177.256 27.4667H177.359V29.5238H181.85Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M184.866 29.5238H189.529V19.3067C189.529 16.9752 190.798 15.4667 192.684 15.4667C194.398 15.4667 195.392 16.4952 195.392 18.4838V29.5238H200.055V19.3067C200.055 16.9752 201.255 15.4667 203.209 15.4667C204.924 15.4667 205.918 16.4952 205.918 18.4838V29.5238H210.581V17.6952C210.581 13.8552 208.489 11.4552 204.786 11.4552C202.558 11.4552 200.706 12.6209 199.506 14.5409H199.438C198.581 12.6895 196.798 11.4552 194.569 11.4552C192.135 11.4552 190.421 12.6895 189.461 14.3009H189.358V11.9352H184.866V29.5238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M0.824158 29.5238H5.48701V5.00952H0.824158V29.5238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M16.8884 30.0381C22.3398 30.0381 26.0769 25.9924 26.0769 20.7467C26.0769 15.5009 22.3398 11.4552 16.8884 11.4552C11.4369 11.4552 7.69978 15.5009 7.69978 20.7467C7.69978 25.9924 11.4369 30.0381 16.8884 30.0381ZM16.8884 26.4724C14.0084 26.4724 12.4312 24.1752 12.4312 20.7467C12.4312 17.3181 14.0084 14.9867 16.8884 14.9867C19.7341 14.9867 21.3455 17.3181 21.3455 20.7467C21.3455 24.1752 19.7341 26.4724 16.8884 26.4724Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M35.993 35.5238C38.5987 35.5238 40.8616 34.9067 42.3358 33.5352C43.6387 32.3352 44.4273 30.6552 44.4273 28.1867V11.9352H39.9359V13.7867H39.8673C38.8044 12.3124 37.193 11.4552 34.9987 11.4552C30.5416 11.4552 27.3873 14.8152 27.3873 20.0609C27.3873 25.3752 31.2273 28.4609 35.1359 28.4609C37.3644 28.4609 38.7016 27.5695 39.7301 26.4038H39.833V28.3238C39.833 30.7238 38.5644 31.9924 35.9244 31.9924C33.7644 31.9924 32.7701 31.1352 32.393 30.0381H27.7644C28.2444 33.4667 31.193 35.5238 35.993 35.5238ZM35.9244 24.7238C33.5244 24.7238 31.9473 22.9752 31.9473 19.9924C31.9473 17.0438 33.5244 15.1924 35.8901 15.1924C38.7016 15.1924 40.073 17.3867 40.073 19.9581C40.073 22.5638 38.873 24.7238 35.9244 24.7238Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M55.7611 30.0381C61.2125 30.0381 64.9497 25.9924 64.9497 20.7467C64.9497 15.5009 61.2125 11.4552 55.7611 11.4552C50.3097 11.4552 46.5725 15.5009 46.5725 20.7467C46.5725 25.9924 50.3097 30.0381 55.7611 30.0381ZM55.7611 26.4724C52.8811 26.4724 51.304 24.1752 51.304 20.7467C51.304 17.3181 52.8811 14.9867 55.7611 14.9867C58.6068 14.9867 60.2183 17.3181 60.2183 20.7467C60.2183 24.1752 58.6068 26.4724 55.7611 26.4724Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' d='M212.275 9.04762C212.275 8.25864 212.915 7.61905 213.704 7.61905H216.561C217.35 7.61905 217.99 8.25864 217.99 9.04762C217.99 9.8366 217.35 10.4762 216.561 10.4762H213.704C212.915 10.4762 212.275 9.8366 212.275 9.04762Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3Cpath class='ccustom' fill-rule='evenodd' clip-rule='evenodd' d='M93.2277 0C104.273 0 113.228 8.95431 113.228 20C113.228 31.0457 104.273 40 93.2277 40C82.182 40 73.2277 31.0457 73.2277 20C73.2277 8.95431 82.182 0 93.2277 0ZM92.5048 1.49659C90.2231 1.81769 88.0505 3.65108 86.364 6.7174C85.8748 7.60683 85.4334 8.58946 85.0488 9.65044C87.342 9.07417 89.8611 8.73442 92.5048 8.68187V1.49659ZM83.3584 10.1308C83.8368 8.62958 84.4219 7.2484 85.0972 6.02065C85.9332 4.50059 86.9254 3.18795 88.0433 2.17977C81.9644 3.94523 77.1729 8.73679 75.4074 14.8157C76.4156 13.6978 77.7282 12.7056 79.2483 11.8696C80.4761 11.1943 81.8572 10.6091 83.3584 10.1308ZM82.8781 11.8211C82.3018 14.1143 81.9621 16.6334 81.9095 19.2771H74.7242C75.0453 16.9954 76.8787 14.8228 79.9451 13.1364C80.8345 12.6472 81.8171 12.2058 82.8781 11.8211ZM83.3556 19.2771C83.4153 16.392 83.8307 13.6834 84.5179 11.2902C86.9111 10.603 89.6197 10.1876 92.5048 10.1279V13.2508C91.4285 16.0062 89.2333 18.2012 86.4778 19.2771H83.3556ZM81.9095 20.7229H74.7242C75.0453 23.0046 76.8787 25.1771 79.9451 26.8636C80.8345 27.3528 81.8171 27.7942 82.8781 28.1789C82.3018 25.8857 81.9621 23.3666 81.9095 20.7229ZM84.5179 28.7098C83.8307 26.3166 83.4153 23.608 83.3556 20.7229H86.4778C89.2333 21.7988 91.4285 23.9938 92.5048 26.7492V29.8721C89.6197 29.8124 86.9111 29.397 84.5179 28.7098ZM83.3584 29.8692C81.8572 29.3909 80.4761 28.8057 79.2483 28.1304C77.7282 27.2944 76.4156 26.3022 75.4074 25.1843C77.1729 31.2632 81.9644 36.0548 88.0433 37.8202C86.9254 36.812 85.9332 35.4994 85.0972 33.9793C84.4219 32.7516 83.8368 31.3704 83.3584 29.8692ZM92.5048 38.5034C90.2231 38.1823 88.0505 36.3489 86.364 33.2826C85.8748 32.3932 85.4334 31.4105 85.0488 30.3496C87.342 30.9258 89.8611 31.2656 92.5048 31.3181V38.5034ZM98.412 37.8202C99.5299 36.812 100.522 35.4994 101.358 33.9793C102.033 32.7516 102.619 31.3704 103.097 29.8692C104.598 29.3909 105.979 28.8057 107.207 28.1304C108.727 27.2944 110.04 26.3022 111.048 25.1843C109.282 31.2632 104.491 36.0548 98.412 37.8202ZM101.407 30.3496C101.022 31.4105 100.58 32.3932 100.091 33.2826C98.4048 36.3489 96.2322 38.1823 93.9505 38.5034V31.3181C96.5942 31.2656 99.1133 30.9258 101.407 30.3496ZM103.577 28.1789C104.638 27.7942 105.621 27.3528 106.51 26.8636C109.577 25.1772 111.41 23.0046 111.731 20.7229H104.546C104.493 23.3666 104.153 25.8857 103.577 28.1789ZM103.1 20.7229C103.04 23.608 102.625 26.3166 101.937 28.7098C99.5442 29.397 96.8356 29.8124 93.9505 29.8721V26.7515C95.0265 23.9951 97.2222 21.7991 99.9784 20.7229H103.1ZM104.546 19.2771H111.731C111.41 16.9954 109.577 14.8228 106.51 13.1364C105.621 12.6472 104.638 12.2058 103.577 11.8211C104.153 14.1143 104.493 16.6334 104.546 19.2771ZM101.937 11.2902C102.625 13.6834 103.04 16.392 103.1 19.2771H99.9785C97.2222 18.2009 95.0265 16.0049 93.9505 13.2485V10.1279C96.8356 10.1876 99.5442 10.603 101.937 11.2902ZM103.097 10.1308C104.598 10.6091 105.979 11.1943 107.207 11.8696C108.727 12.7056 110.04 13.6978 111.048 14.8157C109.282 8.73679 104.491 3.94523 98.412 2.17977C99.5299 3.18795 100.522 4.50059 101.358 6.02065C102.033 7.2484 102.619 8.62958 103.097 10.1308ZM93.9505 1.49659C96.2322 1.81769 98.4048 3.65108 100.091 6.7174C100.58 7.60684 101.022 8.58946 101.407 9.65044C99.1133 9.07417 96.5942 8.73442 93.9505 8.68187V1.49659Z' fill='%23fff' stop-color='%23fff'%3E%3C/path%3E%3C/svg%3E",
							"size": null
						}
					}
				],
				variation: "light"
			}
		});

	component_7 = new Component$8({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Prolan & Co"
				},
				site_nav: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				footer_links: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact Us" }
					}
				],
				heading: "We would enjoy working with you",
				link: { "url": "/contact", "label": "Contact us" },
				variation: "dark"
			}
		});

	component_8 = new Component$9({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Prolan & Co"
				},
				site_nav: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				footer_links: [
					{
						"link": {
							"url": "/work",
							"label": "Work",
							"active": false
						}
					},
					{
						"link": {
							"url": "/services",
							"label": "Services",
							"active": false
						}
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact Us" }
					}
				]
			}
		});

	component_9 = new Component$a({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Prolan & Co"
				},
				site_nav: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact" }
					}
				],
				footer_links: [
					{
						"link": { "url": "/work", "label": "Work" }
					},
					{
						"link": { "url": "/services", "label": "Services" }
					},
					{
						"link": { "url": "/company", "label": "Company" }
					},
					{
						"link": { "url": "/contact", "label": "Contact Us" }
					}
				]
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
			t6 = space();
			create_component(component_7.$$.fragment);
			t7 = space();
			create_component(component_8.$$.fragment);
			t8 = space();
			create_component(component_9.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
			t6 = claim_space(nodes);
			claim_component(component_7.$$.fragment, nodes);
			t7 = claim_space(nodes);
			claim_component(component_8.$$.fragment, nodes);
			t8 = claim_space(nodes);
			claim_component(component_9.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			insert_hydration(target, t6, anchor);
			mount_component(component_7, target, anchor);
			insert_hydration(target, t7, anchor);
			mount_component(component_8, target, anchor);
			insert_hydration(target, t8, anchor);
			mount_component(component_9, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			transition_in(component_7.$$.fragment, local);
			transition_in(component_8.$$.fragment, local);
			transition_in(component_9.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			transition_out(component_7.$$.fragment, local);
			transition_out(component_8.$$.fragment, local);
			transition_out(component_9.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
			if (detaching) detach(t6);
			destroy_component(component_7, detaching);
			if (detaching) detach(t7);
			destroy_component(component_8, detaching);
			if (detaching) detach(t8);
			destroy_component(component_9, detaching);
		}
	};
}

class Component$b extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$a, safe_not_equal, {});
	}
}

export default Component$b;
