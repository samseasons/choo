import { html } from './choo.js'

export const process = (state, emit) => {
  emit.on('change', (a1, a2) => {
    if (!state[a1]) state[a1] = a2
  })
}

export const load = (state, emit) => {
  const loads = {}
  Object.assign(state, loads)
  emit('change', 'arg1', 'arg2')
}

export const route = (state, emit) => {
  return html`<div id='xo'>${html`water`}</div>`
}