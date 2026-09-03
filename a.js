import { choo } from './y/choo.js'
import { load, process, route } from './y/load.js'

const choos = new choo()
choos.use(process)
choos.load(load)
choos.route(route)
choos.mount('xo')